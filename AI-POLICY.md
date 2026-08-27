# AI policy

This file is the human-facing contract for AI-assisted contributions to Physlib. AI agent instructions are in [AGENTS.md](AGENTS.md).

## 1. Introduction

1.1. Physlib generally welcomes AI-assisted contributions.

1.2. If you use an AI tool to help author a pull request to Physlib, you must follow the guidelines in this file, and ensure your agent follows [AGENTS.md](AGENTS.md).

1.3. Failure to follow these guidelines may result in your PR being closed without comment after a brief triage. Repeated failures may result in being banned from contributing to the project. This is to protect the project and the time of the maintainers.

1.4. Throughout this document, "must" denotes a hard requirement and "should" denotes a strong expectation that is not strictly enforced.

1.5. You must also follow any explicit instructions in [docs/ReviewGuidelines.md](docs/ReviewGuidelines.md).

1.6. These guidelines apply to any contribution where an AI tool produced more than trivial assistance.

1.7. The human author(s) are fully responsible for every line of the PR, however it was produced. A human must vouch that each definition, theorem statement, and proof step means what it claims. A clean Lean build proves what was written, but only the human can certify what was written is what they meant.

## 2. Author obligations

2.1. You must verify any bibliographic references for correctness yourself: that the work exists, that the cited statement is accurate, and that page numbers are right. This must not be delegated to an AI.

2.2. You must confirm your contribution satisfies the content and structure rules in [AGENTS.md](AGENTS.md) before opening the PR. The agent's compliance is your responsibility, not the reviewer's.

## 3. Review process

3.1. All communication with human reviewers must be conducted by humans, not by an AI agent.

3.2. If an AI agent is used to implement reviewer feedback, the author must independently verify that the feedback has been addressed correctly before requesting re-review. This must not be left to the reviewer to check.
