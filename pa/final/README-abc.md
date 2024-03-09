[![.github/workflows/build-posix.yml](https://github.com/berkeley-abc/abc/actions/workflows/build-posix.yml/badge.svg)](https://github.com/berkeley-abc/abc/actions/workflows/build-posix.yml)
[![.github/workflows/build-windows.yml](https://github.com/berkeley-abc/abc/actions/workflows/build-windows.yml/badge.svg)](https://github.com/berkeley-abc/abc/actions/workflows/build-windows.yml)
[![.github/workflows/build-posix-cmake.yml](https://github.com/berkeley-abc/abc/actions/workflows/build-posix-cmake.yml/badge.svg)](https://github.com/berkeley-abc/abc/actions/workflows/build-posix-cmake.yml)

## Submission Workflow
We will follow a common [git feature branch workflow](https://www.atlassian.com/git/tutorials/comparing-workflows/feature-branch-workflow) for submission.
Programming assignments **must** be submitted via a pull request to a student's branch.
All enrolled students will have their own branches named by their students' ID numbers.
If you cannot find your own branch, please contact the TA.
If you don't know how to create a pull request, please read through this [document](https://guides.github.com/activities/forking/).

We will allocate a period of time for submission.
Outside the submission period this repository will be locked down: it will not accept any pull request.
You **must** create a pull request during the submission period.

### To avoid plagiarism ...
Please note that your fork of this public repository will also be public,
which means that if you push your code to the fork, it is visible to everyone.
In case you want to prevent other students from copying your solution,
an easy way is to push and create a pull request at the last moment before the deadline.

Another complicated way is to create a private repository to develop your solutions,
pull your code to the public fork after an assignment is finished,
and create a pull request via the public fork.
The benefit of this method is that you can push your code during the development and keep it private.
The drawback is again you need to create a pull request close to the deadline, as PRs are visible to everyone.
The detailed steps are documented [here](./private-fork.md).

## Assignments
### PA0
Topic: Getting familiar with git and GitHub

Task: Fill in your GitHub Account in this [table](./lsv/admin/participants-id.csv) via a pull request to the **master** branch.

Deadline: 2021/10/04 

### [PA1](./lsv/pa1/README.md)
Topic: Finding maximum single-fanout cones (MSFCs)

Submission period:
- Parts 1 and 2: 2021/10/08 11:00-13:00 
- Part 3: 2021/10/22 11:00-13:00 

### [PA2](./lsv/pa2/README.md)
Topic: OR Bi-Decomposition of Functions 

Submission period: 2021/12/24 11:00-13:00 

#### Evaluation
For PA1 and PA2, your submissions will be evaluated over [The EPFL Combinational Benchmark Suite](https://www.epfl.ch/labs/lsi/page-102566-en-html/benchmarks/).
You can clone the benchmarks from this [repository](https://github.com/lsils/benchmarks) and create a symbolic link in your PA folder.

```
~$ git clone git@github.com:lsils/benchmarks.git EPFL-benchmark-suite
~$ cd LSV-PA
~/LSV-PA$ ln -s ~/EPFL-benchmark-suite ./benchmarks
```

## Participants
We recommend students to register their student IDs and GitHub accounts in this [table](./lsv/admin/participants-id.csv).

## Contact
TA: Yun-Rong Luo (r10943108@ntu.edu.tw)

For questions, you are encouraged to open an [issue](https://github.com/NTU-ALComLab/LSV-PA/issues).
As other students might have the same questions, discussing in an issue will benefit everyone.
Note that you can set labels, e.g., `PA0`, `PA1`, etc, to classify your questions.
