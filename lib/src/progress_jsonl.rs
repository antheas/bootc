//! Output progress data using the json-lines format. For more information
//! see <https://jsonlines.org/>.

use std::fs;
use std::io::{BufWriter, Write};
use std::os::fd::{FromRawFd, RawFd};

use anyhow::Result;
use serde::Serialize;

#[derive(Debug, serde::Serialize, serde::Deserialize)]
pub struct LayerState {
    pub digest: String,
    pub downloaded: u64,
    pub size: u64,
    /// "cached", "waiting", "downloading", "done"
    pub status: String,
}

#[derive(Debug, serde::Serialize, serde::Deserialize)]
#[serde(tag = "stage")]
pub enum ProgressStage {
    #[serde(rename = "fetching")]
    Fetching {
        bytes_done: u64,
        bytes_download: u64,
        bytes_total: u64,
        layers_done: usize,
        layers_download: usize,
        layers_total: usize,
        layers: Option<Vec<LayerState>>,
    },
}

pub(crate) struct ProgressWriter {
    fd: BufWriter<fs::File>,
    closed: bool,
}

impl From<fs::File> for ProgressWriter {
    fn from(value: fs::File) -> Self {
        Self {
            fd: BufWriter::new(value),
            closed: false,
        }
    }
}

impl ProgressWriter {
    /// Given a raw file descriptor, create an instance of a json-lines writer.
    #[allow(unsafe_code)]
    pub(crate) fn from_raw_fd(fd: RawFd) -> Self {
        unsafe { fs::File::from_raw_fd(fd) }.into()
    }

    /// Serialize the target object to JSON as a single line
    pub(crate) fn send_unchecked<T: Serialize>(&mut self, v: T) -> Result<()> {
        // serde is guaranteed not to output newlines here
        serde_json::to_writer(&mut self.fd, &v)?;
        // We always end in a newline
        self.fd.write_all(b"\n")?;
        // And flush to ensure the remote side sees updates immediately
        self.fd.flush()?;
        Ok(())
    }

    pub(crate) fn send<T: Serialize>(&mut self, v: T) {
        if self.closed {
            return;
        }
        if let Err(e) = self.send_unchecked(v) {
            eprintln!("Failed to write to jsonl: {}", e);
            // Stop writing to fd but let process continue
            self.closed = true;
        }
    }

    /// Flush remaining data and return the underlying file.
    #[allow(dead_code)]
    pub(crate) fn into_inner(self) -> Result<fs::File> {
        self.fd.into_inner().map_err(Into::into)
    }
}

#[cfg(test)]
mod test {
    use std::io::{BufRead, BufReader, Seek};

    use serde::Deserialize;

    use super::*;

    #[derive(Serialize, Deserialize, PartialEq, Eq, Debug)]
    struct S {
        s: String,
        v: u32,
    }

    #[test]
    fn test_jsonl() -> Result<()> {
        let tf = tempfile::tempfile()?;
        let mut w = ProgressWriter::from(tf);
        let testvalues = [
            S {
                s: "foo".into(),
                v: 42,
            },
            S {
                // Test with an embedded newline to sanity check that serde doesn't write it literally
                s: "foo\nbar".into(),
                v: 0,
            },
        ];
        for value in &testvalues {
            w.send(value);
        }
        let mut tf = w.into_inner().unwrap();
        tf.seek(std::io::SeekFrom::Start(0))?;
        let tf = BufReader::new(tf);
        for (line, expected) in tf.lines().zip(testvalues.iter()) {
            let line = line?;
            let found: S = serde_json::from_str(&line)?;
            assert_eq!(&found, expected);
        }
        Ok(())
    }
}
