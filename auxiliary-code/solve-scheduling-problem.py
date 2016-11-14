#!/usr/bin/env python
"""
This script employs Z3 to solve the problem of scheduling N jobs on M machines.
Each job is defined by the execution time. Each job can be assigned to one
machine only because each job needs to be executed once only.
Jobs, assigned to the same machine cannot overlap in execution time.
These and a couple of other conditions can be encoded in difference logic over
reals (QF_RDL).

Note: Z3 should be installed since the script uses Z3 python API, see
http://z3prover.github.io/api/html/namespacez3py.html

Example of usage:
python solve-scheduling-problem.py 3 10.04,5,15.5,22.1,3.3 25.5 \
    --pathToZ3 "C:\\Users\\Vasya Pupkin\\projects\\z3-4.5.0-x64-win"
"""
import sys
import os
import argparse


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
    parser.add_argument(
        '--pathToZ3',
        help='path to Z3 solver'
             ' e.g. "C:\\Users\\Vasya Pupkin\\projects\\z3-4.5.0-x64-win"'
    )
    args = parser.parse_args()

    if args.pathToZ3:
        os.environ['PATH'] += os.pathsep + os.path.join(args.pathToZ3, 'bin')
        sys.path.append(os.path.join(args.pathToZ3, 'bin', 'python'))

    numberOfMachines = int(args.numberOfMachines)
    durationOfJobs = [float(job) for job in args.durationOfJobs.split(',')]
    numberOfJobs = len(durationOfJobs)
    totalDuration = float(args.totalDuration)

    from z3 import SolverFor, \
        Real, Bool, \
        And, Or, Not, Implies, \
        sat, is_true, simplify, \
        ArithRef, AlgebraicNumRef, IntNumRef, RatNumRef

    solver = SolverFor('QF_RDL')
    jobStartTimes = [
        Real('t{}'.format(j))
        for j in range(numberOfJobs)
        ]
    machineJobFlags = [
        [Bool('p_{}_{}'.format(m, j)) for j in range(numberOfJobs)]
        for m in range(numberOfMachines)
        ]

    # Every job is executed on at least one machine
    for j in range(numberOfJobs):
        orArgs = [machineJobFlags[m][j] for m in range(numberOfMachines)]
        solver.add(Or(*orArgs))

    # Job is scheduled on one machine only
    for m in range(numberOfMachines):
        for j in range(numberOfJobs):
            orArgs = [
                machineJobFlags[otherM][j]
                for otherM in range(numberOfMachines) if otherM != m
                ]
            condition = Implies(
                machineJobFlags[m][j],
                Not(Or(*orArgs))
            )
            solver.add(condition)

    # Start times cannot be negative
    for jst in jobStartTimes:
        solver.add(0 <= jst)

    # Jobs finish times should not exceed the given total duration
    for jst, jd in zip(jobStartTimes, durationOfJobs):
        condition = jst <= totalDuration - jd
        solver.add(condition)

    # Jobs must not overlap when assigned to the same machine
    numberOfJobs = len(durationOfJobs)
    for m in range(numberOfMachines):
        for j1 in range(numberOfJobs - 1):
            for j2 in range(j1 + 1, numberOfJobs):
                j1OnM = machineJobFlags[m][j1]
                j2OnM = machineJobFlags[m][j2]
                j1AndJ2OnM = And(j1OnM, j2OnM)
                t1 = jobStartTimes[j1]
                t2 = jobStartTimes[j2]
                tau1 = durationOfJobs[j1]
                tau2 = durationOfJobs[j2]
                j1Earlier = t1 - t2 <= -tau1
                j2Earlier = t2 - t1 <= -tau2
                condition = Implies(j1AndJ2OnM, Or(j1Earlier, j2Earlier))
                solver.add(condition)

    satStatus = solver.check()
    print('problem status is: {}'.format(satStatus))
    if satStatus == sat:
        model = solver.model()
        for m in range(numberOfMachines):
            print('schedule for machine {}'.format(m))
            for j in range(numberOfJobs):
                mjf = model[machineJobFlags[m][j]]
                if is_true(mjf):
                    jst = simplify(model[jobStartTimes[j]])
                    assert isinstance(jst, ArithRef)
                    if isinstance(jst, AlgebraicNumRef):
                        jst = float(jst.approx(precision=5))
                    elif isinstance(jst, IntNumRef):
                        jst = float(jst.as_long())
                    elif isinstance(jst, RatNumRef):
                        jst = float(jst.as_fraction())
                    tau = durationOfJobs[j]
                    jft = jst + tau
                    print(
                        'job {}: {} -- {} (duration {})'.format(
                            j, jst, jft, tau
                        )
                    )
            print()

    print('done')


if __name__ == '__main__':
    main()
