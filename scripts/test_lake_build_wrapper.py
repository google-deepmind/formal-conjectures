# Copyright 2026 The Formal Conjectures Authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Unit tests for scripts/lake-build-wrapper.py."""

import importlib
import io
import json
import os
import tempfile
import unittest
from unittest.mock import patch

wrapper = importlib.import_module("lake-build-wrapper")


class BuildOutputProcessorTest(unittest.TestCase):

    def setUp(self):
        self.processor = wrapper.BuildOutputProcessor()

    def test_normal_lines_grouping(self):
        output = io.StringIO()
        with patch("sys.stdout", output):
            self.processor.process_line("✔ [1/10] Built Module1\n")
            self.processor.process_line("✔ [2/10] Built Module2\n")
            self.processor.finalize()

        captured = output.getvalue()
        self.assertIn("::group::Build progress [starting at 1/10]", captured)
        self.assertIn("::endgroup::", captured)
        summary = self.processor.get_summary()
        self.assertEqual(summary["error_count"], 0)
        self.assertEqual(summary["warning_count"], 0)

    def test_error_line_detection_and_summary(self):
        output = io.StringIO()
        with patch("sys.stdout", output):
            self.processor.process_line("✔ [1/2] Built Module1\n")
            self.processor.process_line("✖ [2/2] Building Module2\n")
            self.processor.process_line("error: Module2.lean:10:5: unknown identifier\n")
            self.processor.process_line("error: build failed\n")
            self.processor.finalize()

        captured = output.getvalue()
        self.assertIn("::group::\x1b[31m✖ [2/2] Building Module2\x1b[0m", captured)
        summary = self.processor.get_summary()
        self.assertEqual(summary["error_count"], 1)
        self.assertEqual(len(summary["errors"]), 1)
        self.assertIn("error: Module2.lean:10:5: unknown identifier", summary["errors"][0]["messages"])

    def test_warning_line_detection_and_summary(self):
        output = io.StringIO()
        with patch("sys.stdout", output):
            self.processor.process_line("⚠ [1/1] Built Module1\n")
            self.processor.process_line("warning: Module1.lean:5:0: unused variable\n")
            self.processor.process_line("Build completed successfully (1 job).\n")
            self.processor.finalize()

        summary = self.processor.get_summary()
        self.assertEqual(summary["warning_count"], 1)
        self.assertEqual(len(summary["warnings"]), 1)
        self.assertIn("warning: Module1.lean:5:0: unused variable", summary["warnings"][0]["messages"])


if __name__ == "__main__":
    unittest.main()
