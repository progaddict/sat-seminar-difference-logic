#!/usr/bin/env python
"""
This script generates smt2 file which formulates the problem of scheduling
N jobs on M machines. Each job is defined by the execution time. Each job can
be assigned to one machine only because each job needs to be executed once
only. Jobs, assigned to the same machine cannot overlap in execution time.
These and a couple of other conditions can be encoded in difference logic
over reals (QF_RDL).

Example of usage:
python generate-scheduling-problem.py 3 10.04,5,15.5,22.1,3.3 25.5
"""
import argparse

TEMPLATE_JOB_START = 't{}'
TEMPLATE_MACHINE_JOB = 'p_{}_{}'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        'numberOfMachines',
        help='number of available machines e.g. 3'
    )
    parser.add_argument(
        'durationOfJobs',
        help='duration of the jobs to be scheduled'
             ' e.g. "10.04,5,15.5,22.1,3.3"'
    )
    parser.add_argument(
        'totalDuration',
        help='maximal duration of the whole process e.g. 30.55'
    )
    args = parser.parse_args()
    numberOfMachines = int(args.numberOfMachines)
    durationOfJobs = [float(job) for job in args.durationOfJobs.split(',')]
    numberOfJobs = len(durationOfJobs)
    totalDuration = float(args.totalDuration)
    outputFileName = 'scheduling-problem-{}-{}.smt2'.format(
        numberOfMachines,
        numberOfJobs
    )
    with open(outputFileName, 'w') as f:
        putComment(f, 'example scheduling problem')
        putComment(f, 'number of machines = {}'.format(args.numberOfMachines))
        putComment(f, 'duration of jobs = {}'.format(args.durationOfJobs))
        putComment(f, 'total duration = {}'.format(args.totalDuration))
        f.write('(set-logic QF_RDL)\n')
        declareVariables(f, numberOfMachines, numberOfJobs)
        everyJobIsExecutedAtLeastOnce(f, numberOfMachines, numberOfJobs)
        oneMachinePerJobOnly(f, numberOfMachines, numberOfJobs)
        startTimeMustBeNonnegative(f, numberOfJobs)
        jobsShouldNotOverlap(f, numberOfMachines, durationOfJobs)
        jobsShouldNotExceedTotalDuration(f, durationOfJobs, totalDuration)
        f.write('(check-sat)\n')
        f.write('(exit)\n')


def declareVariables(f, numberOfMachines, numberOfJobs):
    putComment(f, 'start times of jobs')
    for j in range(numberOfJobs):
        name = TEMPLATE_JOB_START.format(j)
        declareConst(f, name)
    exampleName = TEMPLATE_MACHINE_JOB.format('m', 'j')
    putComment(
        f,
        '{} = True if machine m was used to execute job j'.format(exampleName)
    )
    for m in range(numberOfMachines):
        for j in range(numberOfJobs):
            name = TEMPLATE_MACHINE_JOB.format(m, j)
            declareConst(f, name, 'Bool')


def everyJobIsExecutedAtLeastOnce(f, numberOfMachines, numberOfJobs):
    """
    Every job is executed on at least one machine.
    """
    for j in range(numberOfJobs):
        jOnAllMachines = [
            TEMPLATE_MACHINE_JOB.format(m, j)
            for m in range(numberOfMachines)
            ]
        s = ' '.join(jOnAllMachines)
        putComment(f, 'job {} is executed on some of the machines'.format(j))
        f.write('(assert (or {}))\n'.format(s))


def oneMachinePerJobOnly(f, numberOfMachines, numberOfJobs):
    """
    If job is executed on machine A then it is not executed on any other
    machine (B, C, D etc.).
    """
    for m in range(numberOfMachines):
        for j in range(numberOfJobs):
            jExecutedOnM = TEMPLATE_MACHINE_JOB.format(m, j)
            otherMachineIdx = list(range(numberOfMachines))
            otherMachineIdx.remove(m)
            otherMachineNames = [
                TEMPLATE_MACHINE_JOB.format(otherM, j)
                for otherM in otherMachineIdx
                ]
            putComment(f, 'if job {} is executed on machine {}'.format(j, m))
            putComment(f, 'then it should not be assigned to other machines')
            f.write('(assert (=> {} (not (or {}))))\n'.format(
                jExecutedOnM,
                ' '.join(otherMachineNames)
            ))


def jobsShouldNotOverlap(f, numberOfMachines, durationOfJobs):
    """
    If job 1 and job 1 are on the same machine then the time spans
    during which these jobs are executed should not overlap:

    t1 + tau1 <= t2   (1 is earlier)
    or
    t2 + tau2 <= t1  (2 is earlier)

    Equivalent formulation in real difference logic:
    t1 - t2 <= -tau1   or   t2 - t1 <= -tau2

    Note: tau1 and tau2 are known constants, t1 and t2 are variables.
    """
    putComment(f, 'no overlap rules')
    numberOfJobs = len(durationOfJobs)
    for m in range(numberOfMachines):
        for j1 in range(numberOfJobs - 1):
            for j2 in range(j1 + 1, numberOfJobs):
                j1OnM = TEMPLATE_MACHINE_JOB.format(m, j1)
                j2OnM = TEMPLATE_MACHINE_JOB.format(m, j2)
                j1AndJ2OnM = '(and {} {})'.format(j1OnM, j2OnM)
                t1 = TEMPLATE_JOB_START.format(j1)
                t2 = TEMPLATE_JOB_START.format(j2)
                tau1 = durationOfJobs[j1]
                tau2 = durationOfJobs[j2]
                j1Earlier = '(<= (- {} {}) {})'.format(t1, t2, -tau1)
                j2Earlier = '(<= (- {} {}) {})'.format(t2, t1, -tau2)
                f.write('(assert (=> {} (or {} {})))\n'.format(
                    j1AndJ2OnM,
                    j1Earlier,
                    j2Earlier
                ))


def startTimeMustBeNonnegative(f, numberOfJobs):
    """
    Start time tj of a job j should be nonnegative:

    tj >= 0

    Equivalent formulation:
    0 <= tj
    """
    putComment(f, 'jobs cannot start at negative times')
    for j in range(numberOfJobs):
        condition = '(<= 0 {})'.format(TEMPLATE_JOB_START.format(j))
        f.write('(assert {})\n'.format(condition))


def jobsShouldNotExceedTotalDuration(f, durationOfJobs, totalDuration):
    """
    Given the total duration T it should be enforced that any job will be
    finished not later than T:

    t1 + tau1 <= T

    Equivalent formulation:
    t1 <= T - tau1

    Note: T and tau1 are known constants, t1 is a variable
    """
    putComment(f, 'jobs are limited by the global total duration time')
    for idx, jd in enumerate(durationOfJobs):
        condition = '(<= {} {})'.format(
            TEMPLATE_JOB_START.format(idx),
            totalDuration - jd
        )
        f.write('(assert {})\n'.format(condition))


def putComment(f, text):
    f.write('; {}\n'.format(text))


def declareConst(f, name, type='Real'):
    f.write('(declare-const {} {})\n'.format(name, type))


def setConstValue(f, name, value):
    f.write('(assert (= {} {}))\n'.format(name, value))


if __name__ == '__main__':
    main()
