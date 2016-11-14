; example scheduling problem
; number of machines = 2
; duration of jobs = 5,5,5,5
; total duration = 10
(set-logic QF_RDL)
; start times of jobs
(declare-const t0 Real)
(declare-const t1 Real)
(declare-const t2 Real)
(declare-const t3 Real)
; p_m_j = True if machine m was used to execute job j
(declare-const p_0_0 Bool)
(declare-const p_0_1 Bool)
(declare-const p_0_2 Bool)
(declare-const p_0_3 Bool)
(declare-const p_1_0 Bool)
(declare-const p_1_1 Bool)
(declare-const p_1_2 Bool)
(declare-const p_1_3 Bool)
; job 0 is executed on some of the machines
(assert (or p_0_0 p_1_0))
; job 1 is executed on some of the machines
(assert (or p_0_1 p_1_1))
; job 2 is executed on some of the machines
(assert (or p_0_2 p_1_2))
; job 3 is executed on some of the machines
(assert (or p_0_3 p_1_3))
; if job 0 is executed on machine 0
; then it should not be assigned to other machines
(assert (=> p_0_0 (not (or p_1_0))))
; if job 1 is executed on machine 0
; then it should not be assigned to other machines
(assert (=> p_0_1 (not (or p_1_1))))
; if job 2 is executed on machine 0
; then it should not be assigned to other machines
(assert (=> p_0_2 (not (or p_1_2))))
; if job 3 is executed on machine 0
; then it should not be assigned to other machines
(assert (=> p_0_3 (not (or p_1_3))))
; if job 0 is executed on machine 1
; then it should not be assigned to other machines
(assert (=> p_1_0 (not (or p_0_0))))
; if job 1 is executed on machine 1
; then it should not be assigned to other machines
(assert (=> p_1_1 (not (or p_0_1))))
; if job 2 is executed on machine 1
; then it should not be assigned to other machines
(assert (=> p_1_2 (not (or p_0_2))))
; if job 3 is executed on machine 1
; then it should not be assigned to other machines
(assert (=> p_1_3 (not (or p_0_3))))
; jobs cannot start at negative times
(assert (<= 0 t0))
(assert (<= 0 t1))
(assert (<= 0 t2))
(assert (<= 0 t3))
; no overlap rules
(assert (=> (and p_0_0 p_0_1) (or (<= (- t0 t1) -5.0) (<= (- t1 t0) -5.0))))
(assert (=> (and p_0_0 p_0_2) (or (<= (- t0 t2) -5.0) (<= (- t2 t0) -5.0))))
(assert (=> (and p_0_0 p_0_3) (or (<= (- t0 t3) -5.0) (<= (- t3 t0) -5.0))))
(assert (=> (and p_0_1 p_0_2) (or (<= (- t1 t2) -5.0) (<= (- t2 t1) -5.0))))
(assert (=> (and p_0_1 p_0_3) (or (<= (- t1 t3) -5.0) (<= (- t3 t1) -5.0))))
(assert (=> (and p_0_2 p_0_3) (or (<= (- t2 t3) -5.0) (<= (- t3 t2) -5.0))))
(assert (=> (and p_1_0 p_1_1) (or (<= (- t0 t1) -5.0) (<= (- t1 t0) -5.0))))
(assert (=> (and p_1_0 p_1_2) (or (<= (- t0 t2) -5.0) (<= (- t2 t0) -5.0))))
(assert (=> (and p_1_0 p_1_3) (or (<= (- t0 t3) -5.0) (<= (- t3 t0) -5.0))))
(assert (=> (and p_1_1 p_1_2) (or (<= (- t1 t2) -5.0) (<= (- t2 t1) -5.0))))
(assert (=> (and p_1_1 p_1_3) (or (<= (- t1 t3) -5.0) (<= (- t3 t1) -5.0))))
(assert (=> (and p_1_2 p_1_3) (or (<= (- t2 t3) -5.0) (<= (- t3 t2) -5.0))))
; jobs are limited by the global total duration time
(assert (<= t0 5.0))
(assert (<= t1 5.0))
(assert (<= t2 5.0))
(assert (<= t3 5.0))
(check-sat)
(exit)
