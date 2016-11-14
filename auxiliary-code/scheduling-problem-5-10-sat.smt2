; example scheduling problem
; number of machines = 5
; duration of jobs = 1,2,3,4,5,6,7,8,9,10
; total duration = 11
(set-logic QF_RDL)
; start times of jobs
(declare-const t0 Real)
(declare-const t1 Real)
(declare-const t2 Real)
(declare-const t3 Real)
(declare-const t4 Real)
(declare-const t5 Real)
(declare-const t6 Real)
(declare-const t7 Real)
(declare-const t8 Real)
(declare-const t9 Real)
; p_m_j = True if machine m was used to execute job j
(declare-const p_0_0 Bool)
(declare-const p_0_1 Bool)
(declare-const p_0_2 Bool)
(declare-const p_0_3 Bool)
(declare-const p_0_4 Bool)
(declare-const p_0_5 Bool)
(declare-const p_0_6 Bool)
(declare-const p_0_7 Bool)
(declare-const p_0_8 Bool)
(declare-const p_0_9 Bool)
(declare-const p_1_0 Bool)
(declare-const p_1_1 Bool)
(declare-const p_1_2 Bool)
(declare-const p_1_3 Bool)
(declare-const p_1_4 Bool)
(declare-const p_1_5 Bool)
(declare-const p_1_6 Bool)
(declare-const p_1_7 Bool)
(declare-const p_1_8 Bool)
(declare-const p_1_9 Bool)
(declare-const p_2_0 Bool)
(declare-const p_2_1 Bool)
(declare-const p_2_2 Bool)
(declare-const p_2_3 Bool)
(declare-const p_2_4 Bool)
(declare-const p_2_5 Bool)
(declare-const p_2_6 Bool)
(declare-const p_2_7 Bool)
(declare-const p_2_8 Bool)
(declare-const p_2_9 Bool)
(declare-const p_3_0 Bool)
(declare-const p_3_1 Bool)
(declare-const p_3_2 Bool)
(declare-const p_3_3 Bool)
(declare-const p_3_4 Bool)
(declare-const p_3_5 Bool)
(declare-const p_3_6 Bool)
(declare-const p_3_7 Bool)
(declare-const p_3_8 Bool)
(declare-const p_3_9 Bool)
(declare-const p_4_0 Bool)
(declare-const p_4_1 Bool)
(declare-const p_4_2 Bool)
(declare-const p_4_3 Bool)
(declare-const p_4_4 Bool)
(declare-const p_4_5 Bool)
(declare-const p_4_6 Bool)
(declare-const p_4_7 Bool)
(declare-const p_4_8 Bool)
(declare-const p_4_9 Bool)
; job 0 is executed on some of the machines
(assert (or p_0_0 p_1_0 p_2_0 p_3_0 p_4_0))
; job 1 is executed on some of the machines
(assert (or p_0_1 p_1_1 p_2_1 p_3_1 p_4_1))
; job 2 is executed on some of the machines
(assert (or p_0_2 p_1_2 p_2_2 p_3_2 p_4_2))
; job 3 is executed on some of the machines
(assert (or p_0_3 p_1_3 p_2_3 p_3_3 p_4_3))
; job 4 is executed on some of the machines
(assert (or p_0_4 p_1_4 p_2_4 p_3_4 p_4_4))
; job 5 is executed on some of the machines
(assert (or p_0_5 p_1_5 p_2_5 p_3_5 p_4_5))
; job 6 is executed on some of the machines
(assert (or p_0_6 p_1_6 p_2_6 p_3_6 p_4_6))
; job 7 is executed on some of the machines
(assert (or p_0_7 p_1_7 p_2_7 p_3_7 p_4_7))
; job 8 is executed on some of the machines
(assert (or p_0_8 p_1_8 p_2_8 p_3_8 p_4_8))
; job 9 is executed on some of the machines
(assert (or p_0_9 p_1_9 p_2_9 p_3_9 p_4_9))
; if job 0 is executed on machine 0
; then it should not be assigned to other machines
(assert (=> p_0_0 (not (or p_1_0 p_2_0 p_3_0 p_4_0))))
; if job 1 is executed on machine 0
; then it should not be assigned to other machines
(assert (=> p_0_1 (not (or p_1_1 p_2_1 p_3_1 p_4_1))))
; if job 2 is executed on machine 0
; then it should not be assigned to other machines
(assert (=> p_0_2 (not (or p_1_2 p_2_2 p_3_2 p_4_2))))
; if job 3 is executed on machine 0
; then it should not be assigned to other machines
(assert (=> p_0_3 (not (or p_1_3 p_2_3 p_3_3 p_4_3))))
; if job 4 is executed on machine 0
; then it should not be assigned to other machines
(assert (=> p_0_4 (not (or p_1_4 p_2_4 p_3_4 p_4_4))))
; if job 5 is executed on machine 0
; then it should not be assigned to other machines
(assert (=> p_0_5 (not (or p_1_5 p_2_5 p_3_5 p_4_5))))
; if job 6 is executed on machine 0
; then it should not be assigned to other machines
(assert (=> p_0_6 (not (or p_1_6 p_2_6 p_3_6 p_4_6))))
; if job 7 is executed on machine 0
; then it should not be assigned to other machines
(assert (=> p_0_7 (not (or p_1_7 p_2_7 p_3_7 p_4_7))))
; if job 8 is executed on machine 0
; then it should not be assigned to other machines
(assert (=> p_0_8 (not (or p_1_8 p_2_8 p_3_8 p_4_8))))
; if job 9 is executed on machine 0
; then it should not be assigned to other machines
(assert (=> p_0_9 (not (or p_1_9 p_2_9 p_3_9 p_4_9))))
; if job 0 is executed on machine 1
; then it should not be assigned to other machines
(assert (=> p_1_0 (not (or p_0_0 p_2_0 p_3_0 p_4_0))))
; if job 1 is executed on machine 1
; then it should not be assigned to other machines
(assert (=> p_1_1 (not (or p_0_1 p_2_1 p_3_1 p_4_1))))
; if job 2 is executed on machine 1
; then it should not be assigned to other machines
(assert (=> p_1_2 (not (or p_0_2 p_2_2 p_3_2 p_4_2))))
; if job 3 is executed on machine 1
; then it should not be assigned to other machines
(assert (=> p_1_3 (not (or p_0_3 p_2_3 p_3_3 p_4_3))))
; if job 4 is executed on machine 1
; then it should not be assigned to other machines
(assert (=> p_1_4 (not (or p_0_4 p_2_4 p_3_4 p_4_4))))
; if job 5 is executed on machine 1
; then it should not be assigned to other machines
(assert (=> p_1_5 (not (or p_0_5 p_2_5 p_3_5 p_4_5))))
; if job 6 is executed on machine 1
; then it should not be assigned to other machines
(assert (=> p_1_6 (not (or p_0_6 p_2_6 p_3_6 p_4_6))))
; if job 7 is executed on machine 1
; then it should not be assigned to other machines
(assert (=> p_1_7 (not (or p_0_7 p_2_7 p_3_7 p_4_7))))
; if job 8 is executed on machine 1
; then it should not be assigned to other machines
(assert (=> p_1_8 (not (or p_0_8 p_2_8 p_3_8 p_4_8))))
; if job 9 is executed on machine 1
; then it should not be assigned to other machines
(assert (=> p_1_9 (not (or p_0_9 p_2_9 p_3_9 p_4_9))))
; if job 0 is executed on machine 2
; then it should not be assigned to other machines
(assert (=> p_2_0 (not (or p_0_0 p_1_0 p_3_0 p_4_0))))
; if job 1 is executed on machine 2
; then it should not be assigned to other machines
(assert (=> p_2_1 (not (or p_0_1 p_1_1 p_3_1 p_4_1))))
; if job 2 is executed on machine 2
; then it should not be assigned to other machines
(assert (=> p_2_2 (not (or p_0_2 p_1_2 p_3_2 p_4_2))))
; if job 3 is executed on machine 2
; then it should not be assigned to other machines
(assert (=> p_2_3 (not (or p_0_3 p_1_3 p_3_3 p_4_3))))
; if job 4 is executed on machine 2
; then it should not be assigned to other machines
(assert (=> p_2_4 (not (or p_0_4 p_1_4 p_3_4 p_4_4))))
; if job 5 is executed on machine 2
; then it should not be assigned to other machines
(assert (=> p_2_5 (not (or p_0_5 p_1_5 p_3_5 p_4_5))))
; if job 6 is executed on machine 2
; then it should not be assigned to other machines
(assert (=> p_2_6 (not (or p_0_6 p_1_6 p_3_6 p_4_6))))
; if job 7 is executed on machine 2
; then it should not be assigned to other machines
(assert (=> p_2_7 (not (or p_0_7 p_1_7 p_3_7 p_4_7))))
; if job 8 is executed on machine 2
; then it should not be assigned to other machines
(assert (=> p_2_8 (not (or p_0_8 p_1_8 p_3_8 p_4_8))))
; if job 9 is executed on machine 2
; then it should not be assigned to other machines
(assert (=> p_2_9 (not (or p_0_9 p_1_9 p_3_9 p_4_9))))
; if job 0 is executed on machine 3
; then it should not be assigned to other machines
(assert (=> p_3_0 (not (or p_0_0 p_1_0 p_2_0 p_4_0))))
; if job 1 is executed on machine 3
; then it should not be assigned to other machines
(assert (=> p_3_1 (not (or p_0_1 p_1_1 p_2_1 p_4_1))))
; if job 2 is executed on machine 3
; then it should not be assigned to other machines
(assert (=> p_3_2 (not (or p_0_2 p_1_2 p_2_2 p_4_2))))
; if job 3 is executed on machine 3
; then it should not be assigned to other machines
(assert (=> p_3_3 (not (or p_0_3 p_1_3 p_2_3 p_4_3))))
; if job 4 is executed on machine 3
; then it should not be assigned to other machines
(assert (=> p_3_4 (not (or p_0_4 p_1_4 p_2_4 p_4_4))))
; if job 5 is executed on machine 3
; then it should not be assigned to other machines
(assert (=> p_3_5 (not (or p_0_5 p_1_5 p_2_5 p_4_5))))
; if job 6 is executed on machine 3
; then it should not be assigned to other machines
(assert (=> p_3_6 (not (or p_0_6 p_1_6 p_2_6 p_4_6))))
; if job 7 is executed on machine 3
; then it should not be assigned to other machines
(assert (=> p_3_7 (not (or p_0_7 p_1_7 p_2_7 p_4_7))))
; if job 8 is executed on machine 3
; then it should not be assigned to other machines
(assert (=> p_3_8 (not (or p_0_8 p_1_8 p_2_8 p_4_8))))
; if job 9 is executed on machine 3
; then it should not be assigned to other machines
(assert (=> p_3_9 (not (or p_0_9 p_1_9 p_2_9 p_4_9))))
; if job 0 is executed on machine 4
; then it should not be assigned to other machines
(assert (=> p_4_0 (not (or p_0_0 p_1_0 p_2_0 p_3_0))))
; if job 1 is executed on machine 4
; then it should not be assigned to other machines
(assert (=> p_4_1 (not (or p_0_1 p_1_1 p_2_1 p_3_1))))
; if job 2 is executed on machine 4
; then it should not be assigned to other machines
(assert (=> p_4_2 (not (or p_0_2 p_1_2 p_2_2 p_3_2))))
; if job 3 is executed on machine 4
; then it should not be assigned to other machines
(assert (=> p_4_3 (not (or p_0_3 p_1_3 p_2_3 p_3_3))))
; if job 4 is executed on machine 4
; then it should not be assigned to other machines
(assert (=> p_4_4 (not (or p_0_4 p_1_4 p_2_4 p_3_4))))
; if job 5 is executed on machine 4
; then it should not be assigned to other machines
(assert (=> p_4_5 (not (or p_0_5 p_1_5 p_2_5 p_3_5))))
; if job 6 is executed on machine 4
; then it should not be assigned to other machines
(assert (=> p_4_6 (not (or p_0_6 p_1_6 p_2_6 p_3_6))))
; if job 7 is executed on machine 4
; then it should not be assigned to other machines
(assert (=> p_4_7 (not (or p_0_7 p_1_7 p_2_7 p_3_7))))
; if job 8 is executed on machine 4
; then it should not be assigned to other machines
(assert (=> p_4_8 (not (or p_0_8 p_1_8 p_2_8 p_3_8))))
; if job 9 is executed on machine 4
; then it should not be assigned to other machines
(assert (=> p_4_9 (not (or p_0_9 p_1_9 p_2_9 p_3_9))))
; jobs cannot start at negative times
(assert (<= 0 t0))
(assert (<= 0 t1))
(assert (<= 0 t2))
(assert (<= 0 t3))
(assert (<= 0 t4))
(assert (<= 0 t5))
(assert (<= 0 t6))
(assert (<= 0 t7))
(assert (<= 0 t8))
(assert (<= 0 t9))
; no overlap rules
(assert (=> (and p_0_0 p_0_1) (or (<= (- t0 t1) -1.0) (<= (- t1 t0) -2.0))))
(assert (=> (and p_0_0 p_0_2) (or (<= (- t0 t2) -1.0) (<= (- t2 t0) -3.0))))
(assert (=> (and p_0_0 p_0_3) (or (<= (- t0 t3) -1.0) (<= (- t3 t0) -4.0))))
(assert (=> (and p_0_0 p_0_4) (or (<= (- t0 t4) -1.0) (<= (- t4 t0) -5.0))))
(assert (=> (and p_0_0 p_0_5) (or (<= (- t0 t5) -1.0) (<= (- t5 t0) -6.0))))
(assert (=> (and p_0_0 p_0_6) (or (<= (- t0 t6) -1.0) (<= (- t6 t0) -7.0))))
(assert (=> (and p_0_0 p_0_7) (or (<= (- t0 t7) -1.0) (<= (- t7 t0) -8.0))))
(assert (=> (and p_0_0 p_0_8) (or (<= (- t0 t8) -1.0) (<= (- t8 t0) -9.0))))
(assert (=> (and p_0_0 p_0_9) (or (<= (- t0 t9) -1.0) (<= (- t9 t0) -10.0))))
(assert (=> (and p_0_1 p_0_2) (or (<= (- t1 t2) -2.0) (<= (- t2 t1) -3.0))))
(assert (=> (and p_0_1 p_0_3) (or (<= (- t1 t3) -2.0) (<= (- t3 t1) -4.0))))
(assert (=> (and p_0_1 p_0_4) (or (<= (- t1 t4) -2.0) (<= (- t4 t1) -5.0))))
(assert (=> (and p_0_1 p_0_5) (or (<= (- t1 t5) -2.0) (<= (- t5 t1) -6.0))))
(assert (=> (and p_0_1 p_0_6) (or (<= (- t1 t6) -2.0) (<= (- t6 t1) -7.0))))
(assert (=> (and p_0_1 p_0_7) (or (<= (- t1 t7) -2.0) (<= (- t7 t1) -8.0))))
(assert (=> (and p_0_1 p_0_8) (or (<= (- t1 t8) -2.0) (<= (- t8 t1) -9.0))))
(assert (=> (and p_0_1 p_0_9) (or (<= (- t1 t9) -2.0) (<= (- t9 t1) -10.0))))
(assert (=> (and p_0_2 p_0_3) (or (<= (- t2 t3) -3.0) (<= (- t3 t2) -4.0))))
(assert (=> (and p_0_2 p_0_4) (or (<= (- t2 t4) -3.0) (<= (- t4 t2) -5.0))))
(assert (=> (and p_0_2 p_0_5) (or (<= (- t2 t5) -3.0) (<= (- t5 t2) -6.0))))
(assert (=> (and p_0_2 p_0_6) (or (<= (- t2 t6) -3.0) (<= (- t6 t2) -7.0))))
(assert (=> (and p_0_2 p_0_7) (or (<= (- t2 t7) -3.0) (<= (- t7 t2) -8.0))))
(assert (=> (and p_0_2 p_0_8) (or (<= (- t2 t8) -3.0) (<= (- t8 t2) -9.0))))
(assert (=> (and p_0_2 p_0_9) (or (<= (- t2 t9) -3.0) (<= (- t9 t2) -10.0))))
(assert (=> (and p_0_3 p_0_4) (or (<= (- t3 t4) -4.0) (<= (- t4 t3) -5.0))))
(assert (=> (and p_0_3 p_0_5) (or (<= (- t3 t5) -4.0) (<= (- t5 t3) -6.0))))
(assert (=> (and p_0_3 p_0_6) (or (<= (- t3 t6) -4.0) (<= (- t6 t3) -7.0))))
(assert (=> (and p_0_3 p_0_7) (or (<= (- t3 t7) -4.0) (<= (- t7 t3) -8.0))))
(assert (=> (and p_0_3 p_0_8) (or (<= (- t3 t8) -4.0) (<= (- t8 t3) -9.0))))
(assert (=> (and p_0_3 p_0_9) (or (<= (- t3 t9) -4.0) (<= (- t9 t3) -10.0))))
(assert (=> (and p_0_4 p_0_5) (or (<= (- t4 t5) -5.0) (<= (- t5 t4) -6.0))))
(assert (=> (and p_0_4 p_0_6) (or (<= (- t4 t6) -5.0) (<= (- t6 t4) -7.0))))
(assert (=> (and p_0_4 p_0_7) (or (<= (- t4 t7) -5.0) (<= (- t7 t4) -8.0))))
(assert (=> (and p_0_4 p_0_8) (or (<= (- t4 t8) -5.0) (<= (- t8 t4) -9.0))))
(assert (=> (and p_0_4 p_0_9) (or (<= (- t4 t9) -5.0) (<= (- t9 t4) -10.0))))
(assert (=> (and p_0_5 p_0_6) (or (<= (- t5 t6) -6.0) (<= (- t6 t5) -7.0))))
(assert (=> (and p_0_5 p_0_7) (or (<= (- t5 t7) -6.0) (<= (- t7 t5) -8.0))))
(assert (=> (and p_0_5 p_0_8) (or (<= (- t5 t8) -6.0) (<= (- t8 t5) -9.0))))
(assert (=> (and p_0_5 p_0_9) (or (<= (- t5 t9) -6.0) (<= (- t9 t5) -10.0))))
(assert (=> (and p_0_6 p_0_7) (or (<= (- t6 t7) -7.0) (<= (- t7 t6) -8.0))))
(assert (=> (and p_0_6 p_0_8) (or (<= (- t6 t8) -7.0) (<= (- t8 t6) -9.0))))
(assert (=> (and p_0_6 p_0_9) (or (<= (- t6 t9) -7.0) (<= (- t9 t6) -10.0))))
(assert (=> (and p_0_7 p_0_8) (or (<= (- t7 t8) -8.0) (<= (- t8 t7) -9.0))))
(assert (=> (and p_0_7 p_0_9) (or (<= (- t7 t9) -8.0) (<= (- t9 t7) -10.0))))
(assert (=> (and p_0_8 p_0_9) (or (<= (- t8 t9) -9.0) (<= (- t9 t8) -10.0))))
(assert (=> (and p_1_0 p_1_1) (or (<= (- t0 t1) -1.0) (<= (- t1 t0) -2.0))))
(assert (=> (and p_1_0 p_1_2) (or (<= (- t0 t2) -1.0) (<= (- t2 t0) -3.0))))
(assert (=> (and p_1_0 p_1_3) (or (<= (- t0 t3) -1.0) (<= (- t3 t0) -4.0))))
(assert (=> (and p_1_0 p_1_4) (or (<= (- t0 t4) -1.0) (<= (- t4 t0) -5.0))))
(assert (=> (and p_1_0 p_1_5) (or (<= (- t0 t5) -1.0) (<= (- t5 t0) -6.0))))
(assert (=> (and p_1_0 p_1_6) (or (<= (- t0 t6) -1.0) (<= (- t6 t0) -7.0))))
(assert (=> (and p_1_0 p_1_7) (or (<= (- t0 t7) -1.0) (<= (- t7 t0) -8.0))))
(assert (=> (and p_1_0 p_1_8) (or (<= (- t0 t8) -1.0) (<= (- t8 t0) -9.0))))
(assert (=> (and p_1_0 p_1_9) (or (<= (- t0 t9) -1.0) (<= (- t9 t0) -10.0))))
(assert (=> (and p_1_1 p_1_2) (or (<= (- t1 t2) -2.0) (<= (- t2 t1) -3.0))))
(assert (=> (and p_1_1 p_1_3) (or (<= (- t1 t3) -2.0) (<= (- t3 t1) -4.0))))
(assert (=> (and p_1_1 p_1_4) (or (<= (- t1 t4) -2.0) (<= (- t4 t1) -5.0))))
(assert (=> (and p_1_1 p_1_5) (or (<= (- t1 t5) -2.0) (<= (- t5 t1) -6.0))))
(assert (=> (and p_1_1 p_1_6) (or (<= (- t1 t6) -2.0) (<= (- t6 t1) -7.0))))
(assert (=> (and p_1_1 p_1_7) (or (<= (- t1 t7) -2.0) (<= (- t7 t1) -8.0))))
(assert (=> (and p_1_1 p_1_8) (or (<= (- t1 t8) -2.0) (<= (- t8 t1) -9.0))))
(assert (=> (and p_1_1 p_1_9) (or (<= (- t1 t9) -2.0) (<= (- t9 t1) -10.0))))
(assert (=> (and p_1_2 p_1_3) (or (<= (- t2 t3) -3.0) (<= (- t3 t2) -4.0))))
(assert (=> (and p_1_2 p_1_4) (or (<= (- t2 t4) -3.0) (<= (- t4 t2) -5.0))))
(assert (=> (and p_1_2 p_1_5) (or (<= (- t2 t5) -3.0) (<= (- t5 t2) -6.0))))
(assert (=> (and p_1_2 p_1_6) (or (<= (- t2 t6) -3.0) (<= (- t6 t2) -7.0))))
(assert (=> (and p_1_2 p_1_7) (or (<= (- t2 t7) -3.0) (<= (- t7 t2) -8.0))))
(assert (=> (and p_1_2 p_1_8) (or (<= (- t2 t8) -3.0) (<= (- t8 t2) -9.0))))
(assert (=> (and p_1_2 p_1_9) (or (<= (- t2 t9) -3.0) (<= (- t9 t2) -10.0))))
(assert (=> (and p_1_3 p_1_4) (or (<= (- t3 t4) -4.0) (<= (- t4 t3) -5.0))))
(assert (=> (and p_1_3 p_1_5) (or (<= (- t3 t5) -4.0) (<= (- t5 t3) -6.0))))
(assert (=> (and p_1_3 p_1_6) (or (<= (- t3 t6) -4.0) (<= (- t6 t3) -7.0))))
(assert (=> (and p_1_3 p_1_7) (or (<= (- t3 t7) -4.0) (<= (- t7 t3) -8.0))))
(assert (=> (and p_1_3 p_1_8) (or (<= (- t3 t8) -4.0) (<= (- t8 t3) -9.0))))
(assert (=> (and p_1_3 p_1_9) (or (<= (- t3 t9) -4.0) (<= (- t9 t3) -10.0))))
(assert (=> (and p_1_4 p_1_5) (or (<= (- t4 t5) -5.0) (<= (- t5 t4) -6.0))))
(assert (=> (and p_1_4 p_1_6) (or (<= (- t4 t6) -5.0) (<= (- t6 t4) -7.0))))
(assert (=> (and p_1_4 p_1_7) (or (<= (- t4 t7) -5.0) (<= (- t7 t4) -8.0))))
(assert (=> (and p_1_4 p_1_8) (or (<= (- t4 t8) -5.0) (<= (- t8 t4) -9.0))))
(assert (=> (and p_1_4 p_1_9) (or (<= (- t4 t9) -5.0) (<= (- t9 t4) -10.0))))
(assert (=> (and p_1_5 p_1_6) (or (<= (- t5 t6) -6.0) (<= (- t6 t5) -7.0))))
(assert (=> (and p_1_5 p_1_7) (or (<= (- t5 t7) -6.0) (<= (- t7 t5) -8.0))))
(assert (=> (and p_1_5 p_1_8) (or (<= (- t5 t8) -6.0) (<= (- t8 t5) -9.0))))
(assert (=> (and p_1_5 p_1_9) (or (<= (- t5 t9) -6.0) (<= (- t9 t5) -10.0))))
(assert (=> (and p_1_6 p_1_7) (or (<= (- t6 t7) -7.0) (<= (- t7 t6) -8.0))))
(assert (=> (and p_1_6 p_1_8) (or (<= (- t6 t8) -7.0) (<= (- t8 t6) -9.0))))
(assert (=> (and p_1_6 p_1_9) (or (<= (- t6 t9) -7.0) (<= (- t9 t6) -10.0))))
(assert (=> (and p_1_7 p_1_8) (or (<= (- t7 t8) -8.0) (<= (- t8 t7) -9.0))))
(assert (=> (and p_1_7 p_1_9) (or (<= (- t7 t9) -8.0) (<= (- t9 t7) -10.0))))
(assert (=> (and p_1_8 p_1_9) (or (<= (- t8 t9) -9.0) (<= (- t9 t8) -10.0))))
(assert (=> (and p_2_0 p_2_1) (or (<= (- t0 t1) -1.0) (<= (- t1 t0) -2.0))))
(assert (=> (and p_2_0 p_2_2) (or (<= (- t0 t2) -1.0) (<= (- t2 t0) -3.0))))
(assert (=> (and p_2_0 p_2_3) (or (<= (- t0 t3) -1.0) (<= (- t3 t0) -4.0))))
(assert (=> (and p_2_0 p_2_4) (or (<= (- t0 t4) -1.0) (<= (- t4 t0) -5.0))))
(assert (=> (and p_2_0 p_2_5) (or (<= (- t0 t5) -1.0) (<= (- t5 t0) -6.0))))
(assert (=> (and p_2_0 p_2_6) (or (<= (- t0 t6) -1.0) (<= (- t6 t0) -7.0))))
(assert (=> (and p_2_0 p_2_7) (or (<= (- t0 t7) -1.0) (<= (- t7 t0) -8.0))))
(assert (=> (and p_2_0 p_2_8) (or (<= (- t0 t8) -1.0) (<= (- t8 t0) -9.0))))
(assert (=> (and p_2_0 p_2_9) (or (<= (- t0 t9) -1.0) (<= (- t9 t0) -10.0))))
(assert (=> (and p_2_1 p_2_2) (or (<= (- t1 t2) -2.0) (<= (- t2 t1) -3.0))))
(assert (=> (and p_2_1 p_2_3) (or (<= (- t1 t3) -2.0) (<= (- t3 t1) -4.0))))
(assert (=> (and p_2_1 p_2_4) (or (<= (- t1 t4) -2.0) (<= (- t4 t1) -5.0))))
(assert (=> (and p_2_1 p_2_5) (or (<= (- t1 t5) -2.0) (<= (- t5 t1) -6.0))))
(assert (=> (and p_2_1 p_2_6) (or (<= (- t1 t6) -2.0) (<= (- t6 t1) -7.0))))
(assert (=> (and p_2_1 p_2_7) (or (<= (- t1 t7) -2.0) (<= (- t7 t1) -8.0))))
(assert (=> (and p_2_1 p_2_8) (or (<= (- t1 t8) -2.0) (<= (- t8 t1) -9.0))))
(assert (=> (and p_2_1 p_2_9) (or (<= (- t1 t9) -2.0) (<= (- t9 t1) -10.0))))
(assert (=> (and p_2_2 p_2_3) (or (<= (- t2 t3) -3.0) (<= (- t3 t2) -4.0))))
(assert (=> (and p_2_2 p_2_4) (or (<= (- t2 t4) -3.0) (<= (- t4 t2) -5.0))))
(assert (=> (and p_2_2 p_2_5) (or (<= (- t2 t5) -3.0) (<= (- t5 t2) -6.0))))
(assert (=> (and p_2_2 p_2_6) (or (<= (- t2 t6) -3.0) (<= (- t6 t2) -7.0))))
(assert (=> (and p_2_2 p_2_7) (or (<= (- t2 t7) -3.0) (<= (- t7 t2) -8.0))))
(assert (=> (and p_2_2 p_2_8) (or (<= (- t2 t8) -3.0) (<= (- t8 t2) -9.0))))
(assert (=> (and p_2_2 p_2_9) (or (<= (- t2 t9) -3.0) (<= (- t9 t2) -10.0))))
(assert (=> (and p_2_3 p_2_4) (or (<= (- t3 t4) -4.0) (<= (- t4 t3) -5.0))))
(assert (=> (and p_2_3 p_2_5) (or (<= (- t3 t5) -4.0) (<= (- t5 t3) -6.0))))
(assert (=> (and p_2_3 p_2_6) (or (<= (- t3 t6) -4.0) (<= (- t6 t3) -7.0))))
(assert (=> (and p_2_3 p_2_7) (or (<= (- t3 t7) -4.0) (<= (- t7 t3) -8.0))))
(assert (=> (and p_2_3 p_2_8) (or (<= (- t3 t8) -4.0) (<= (- t8 t3) -9.0))))
(assert (=> (and p_2_3 p_2_9) (or (<= (- t3 t9) -4.0) (<= (- t9 t3) -10.0))))
(assert (=> (and p_2_4 p_2_5) (or (<= (- t4 t5) -5.0) (<= (- t5 t4) -6.0))))
(assert (=> (and p_2_4 p_2_6) (or (<= (- t4 t6) -5.0) (<= (- t6 t4) -7.0))))
(assert (=> (and p_2_4 p_2_7) (or (<= (- t4 t7) -5.0) (<= (- t7 t4) -8.0))))
(assert (=> (and p_2_4 p_2_8) (or (<= (- t4 t8) -5.0) (<= (- t8 t4) -9.0))))
(assert (=> (and p_2_4 p_2_9) (or (<= (- t4 t9) -5.0) (<= (- t9 t4) -10.0))))
(assert (=> (and p_2_5 p_2_6) (or (<= (- t5 t6) -6.0) (<= (- t6 t5) -7.0))))
(assert (=> (and p_2_5 p_2_7) (or (<= (- t5 t7) -6.0) (<= (- t7 t5) -8.0))))
(assert (=> (and p_2_5 p_2_8) (or (<= (- t5 t8) -6.0) (<= (- t8 t5) -9.0))))
(assert (=> (and p_2_5 p_2_9) (or (<= (- t5 t9) -6.0) (<= (- t9 t5) -10.0))))
(assert (=> (and p_2_6 p_2_7) (or (<= (- t6 t7) -7.0) (<= (- t7 t6) -8.0))))
(assert (=> (and p_2_6 p_2_8) (or (<= (- t6 t8) -7.0) (<= (- t8 t6) -9.0))))
(assert (=> (and p_2_6 p_2_9) (or (<= (- t6 t9) -7.0) (<= (- t9 t6) -10.0))))
(assert (=> (and p_2_7 p_2_8) (or (<= (- t7 t8) -8.0) (<= (- t8 t7) -9.0))))
(assert (=> (and p_2_7 p_2_9) (or (<= (- t7 t9) -8.0) (<= (- t9 t7) -10.0))))
(assert (=> (and p_2_8 p_2_9) (or (<= (- t8 t9) -9.0) (<= (- t9 t8) -10.0))))
(assert (=> (and p_3_0 p_3_1) (or (<= (- t0 t1) -1.0) (<= (- t1 t0) -2.0))))
(assert (=> (and p_3_0 p_3_2) (or (<= (- t0 t2) -1.0) (<= (- t2 t0) -3.0))))
(assert (=> (and p_3_0 p_3_3) (or (<= (- t0 t3) -1.0) (<= (- t3 t0) -4.0))))
(assert (=> (and p_3_0 p_3_4) (or (<= (- t0 t4) -1.0) (<= (- t4 t0) -5.0))))
(assert (=> (and p_3_0 p_3_5) (or (<= (- t0 t5) -1.0) (<= (- t5 t0) -6.0))))
(assert (=> (and p_3_0 p_3_6) (or (<= (- t0 t6) -1.0) (<= (- t6 t0) -7.0))))
(assert (=> (and p_3_0 p_3_7) (or (<= (- t0 t7) -1.0) (<= (- t7 t0) -8.0))))
(assert (=> (and p_3_0 p_3_8) (or (<= (- t0 t8) -1.0) (<= (- t8 t0) -9.0))))
(assert (=> (and p_3_0 p_3_9) (or (<= (- t0 t9) -1.0) (<= (- t9 t0) -10.0))))
(assert (=> (and p_3_1 p_3_2) (or (<= (- t1 t2) -2.0) (<= (- t2 t1) -3.0))))
(assert (=> (and p_3_1 p_3_3) (or (<= (- t1 t3) -2.0) (<= (- t3 t1) -4.0))))
(assert (=> (and p_3_1 p_3_4) (or (<= (- t1 t4) -2.0) (<= (- t4 t1) -5.0))))
(assert (=> (and p_3_1 p_3_5) (or (<= (- t1 t5) -2.0) (<= (- t5 t1) -6.0))))
(assert (=> (and p_3_1 p_3_6) (or (<= (- t1 t6) -2.0) (<= (- t6 t1) -7.0))))
(assert (=> (and p_3_1 p_3_7) (or (<= (- t1 t7) -2.0) (<= (- t7 t1) -8.0))))
(assert (=> (and p_3_1 p_3_8) (or (<= (- t1 t8) -2.0) (<= (- t8 t1) -9.0))))
(assert (=> (and p_3_1 p_3_9) (or (<= (- t1 t9) -2.0) (<= (- t9 t1) -10.0))))
(assert (=> (and p_3_2 p_3_3) (or (<= (- t2 t3) -3.0) (<= (- t3 t2) -4.0))))
(assert (=> (and p_3_2 p_3_4) (or (<= (- t2 t4) -3.0) (<= (- t4 t2) -5.0))))
(assert (=> (and p_3_2 p_3_5) (or (<= (- t2 t5) -3.0) (<= (- t5 t2) -6.0))))
(assert (=> (and p_3_2 p_3_6) (or (<= (- t2 t6) -3.0) (<= (- t6 t2) -7.0))))
(assert (=> (and p_3_2 p_3_7) (or (<= (- t2 t7) -3.0) (<= (- t7 t2) -8.0))))
(assert (=> (and p_3_2 p_3_8) (or (<= (- t2 t8) -3.0) (<= (- t8 t2) -9.0))))
(assert (=> (and p_3_2 p_3_9) (or (<= (- t2 t9) -3.0) (<= (- t9 t2) -10.0))))
(assert (=> (and p_3_3 p_3_4) (or (<= (- t3 t4) -4.0) (<= (- t4 t3) -5.0))))
(assert (=> (and p_3_3 p_3_5) (or (<= (- t3 t5) -4.0) (<= (- t5 t3) -6.0))))
(assert (=> (and p_3_3 p_3_6) (or (<= (- t3 t6) -4.0) (<= (- t6 t3) -7.0))))
(assert (=> (and p_3_3 p_3_7) (or (<= (- t3 t7) -4.0) (<= (- t7 t3) -8.0))))
(assert (=> (and p_3_3 p_3_8) (or (<= (- t3 t8) -4.0) (<= (- t8 t3) -9.0))))
(assert (=> (and p_3_3 p_3_9) (or (<= (- t3 t9) -4.0) (<= (- t9 t3) -10.0))))
(assert (=> (and p_3_4 p_3_5) (or (<= (- t4 t5) -5.0) (<= (- t5 t4) -6.0))))
(assert (=> (and p_3_4 p_3_6) (or (<= (- t4 t6) -5.0) (<= (- t6 t4) -7.0))))
(assert (=> (and p_3_4 p_3_7) (or (<= (- t4 t7) -5.0) (<= (- t7 t4) -8.0))))
(assert (=> (and p_3_4 p_3_8) (or (<= (- t4 t8) -5.0) (<= (- t8 t4) -9.0))))
(assert (=> (and p_3_4 p_3_9) (or (<= (- t4 t9) -5.0) (<= (- t9 t4) -10.0))))
(assert (=> (and p_3_5 p_3_6) (or (<= (- t5 t6) -6.0) (<= (- t6 t5) -7.0))))
(assert (=> (and p_3_5 p_3_7) (or (<= (- t5 t7) -6.0) (<= (- t7 t5) -8.0))))
(assert (=> (and p_3_5 p_3_8) (or (<= (- t5 t8) -6.0) (<= (- t8 t5) -9.0))))
(assert (=> (and p_3_5 p_3_9) (or (<= (- t5 t9) -6.0) (<= (- t9 t5) -10.0))))
(assert (=> (and p_3_6 p_3_7) (or (<= (- t6 t7) -7.0) (<= (- t7 t6) -8.0))))
(assert (=> (and p_3_6 p_3_8) (or (<= (- t6 t8) -7.0) (<= (- t8 t6) -9.0))))
(assert (=> (and p_3_6 p_3_9) (or (<= (- t6 t9) -7.0) (<= (- t9 t6) -10.0))))
(assert (=> (and p_3_7 p_3_8) (or (<= (- t7 t8) -8.0) (<= (- t8 t7) -9.0))))
(assert (=> (and p_3_7 p_3_9) (or (<= (- t7 t9) -8.0) (<= (- t9 t7) -10.0))))
(assert (=> (and p_3_8 p_3_9) (or (<= (- t8 t9) -9.0) (<= (- t9 t8) -10.0))))
(assert (=> (and p_4_0 p_4_1) (or (<= (- t0 t1) -1.0) (<= (- t1 t0) -2.0))))
(assert (=> (and p_4_0 p_4_2) (or (<= (- t0 t2) -1.0) (<= (- t2 t0) -3.0))))
(assert (=> (and p_4_0 p_4_3) (or (<= (- t0 t3) -1.0) (<= (- t3 t0) -4.0))))
(assert (=> (and p_4_0 p_4_4) (or (<= (- t0 t4) -1.0) (<= (- t4 t0) -5.0))))
(assert (=> (and p_4_0 p_4_5) (or (<= (- t0 t5) -1.0) (<= (- t5 t0) -6.0))))
(assert (=> (and p_4_0 p_4_6) (or (<= (- t0 t6) -1.0) (<= (- t6 t0) -7.0))))
(assert (=> (and p_4_0 p_4_7) (or (<= (- t0 t7) -1.0) (<= (- t7 t0) -8.0))))
(assert (=> (and p_4_0 p_4_8) (or (<= (- t0 t8) -1.0) (<= (- t8 t0) -9.0))))
(assert (=> (and p_4_0 p_4_9) (or (<= (- t0 t9) -1.0) (<= (- t9 t0) -10.0))))
(assert (=> (and p_4_1 p_4_2) (or (<= (- t1 t2) -2.0) (<= (- t2 t1) -3.0))))
(assert (=> (and p_4_1 p_4_3) (or (<= (- t1 t3) -2.0) (<= (- t3 t1) -4.0))))
(assert (=> (and p_4_1 p_4_4) (or (<= (- t1 t4) -2.0) (<= (- t4 t1) -5.0))))
(assert (=> (and p_4_1 p_4_5) (or (<= (- t1 t5) -2.0) (<= (- t5 t1) -6.0))))
(assert (=> (and p_4_1 p_4_6) (or (<= (- t1 t6) -2.0) (<= (- t6 t1) -7.0))))
(assert (=> (and p_4_1 p_4_7) (or (<= (- t1 t7) -2.0) (<= (- t7 t1) -8.0))))
(assert (=> (and p_4_1 p_4_8) (or (<= (- t1 t8) -2.0) (<= (- t8 t1) -9.0))))
(assert (=> (and p_4_1 p_4_9) (or (<= (- t1 t9) -2.0) (<= (- t9 t1) -10.0))))
(assert (=> (and p_4_2 p_4_3) (or (<= (- t2 t3) -3.0) (<= (- t3 t2) -4.0))))
(assert (=> (and p_4_2 p_4_4) (or (<= (- t2 t4) -3.0) (<= (- t4 t2) -5.0))))
(assert (=> (and p_4_2 p_4_5) (or (<= (- t2 t5) -3.0) (<= (- t5 t2) -6.0))))
(assert (=> (and p_4_2 p_4_6) (or (<= (- t2 t6) -3.0) (<= (- t6 t2) -7.0))))
(assert (=> (and p_4_2 p_4_7) (or (<= (- t2 t7) -3.0) (<= (- t7 t2) -8.0))))
(assert (=> (and p_4_2 p_4_8) (or (<= (- t2 t8) -3.0) (<= (- t8 t2) -9.0))))
(assert (=> (and p_4_2 p_4_9) (or (<= (- t2 t9) -3.0) (<= (- t9 t2) -10.0))))
(assert (=> (and p_4_3 p_4_4) (or (<= (- t3 t4) -4.0) (<= (- t4 t3) -5.0))))
(assert (=> (and p_4_3 p_4_5) (or (<= (- t3 t5) -4.0) (<= (- t5 t3) -6.0))))
(assert (=> (and p_4_3 p_4_6) (or (<= (- t3 t6) -4.0) (<= (- t6 t3) -7.0))))
(assert (=> (and p_4_3 p_4_7) (or (<= (- t3 t7) -4.0) (<= (- t7 t3) -8.0))))
(assert (=> (and p_4_3 p_4_8) (or (<= (- t3 t8) -4.0) (<= (- t8 t3) -9.0))))
(assert (=> (and p_4_3 p_4_9) (or (<= (- t3 t9) -4.0) (<= (- t9 t3) -10.0))))
(assert (=> (and p_4_4 p_4_5) (or (<= (- t4 t5) -5.0) (<= (- t5 t4) -6.0))))
(assert (=> (and p_4_4 p_4_6) (or (<= (- t4 t6) -5.0) (<= (- t6 t4) -7.0))))
(assert (=> (and p_4_4 p_4_7) (or (<= (- t4 t7) -5.0) (<= (- t7 t4) -8.0))))
(assert (=> (and p_4_4 p_4_8) (or (<= (- t4 t8) -5.0) (<= (- t8 t4) -9.0))))
(assert (=> (and p_4_4 p_4_9) (or (<= (- t4 t9) -5.0) (<= (- t9 t4) -10.0))))
(assert (=> (and p_4_5 p_4_6) (or (<= (- t5 t6) -6.0) (<= (- t6 t5) -7.0))))
(assert (=> (and p_4_5 p_4_7) (or (<= (- t5 t7) -6.0) (<= (- t7 t5) -8.0))))
(assert (=> (and p_4_5 p_4_8) (or (<= (- t5 t8) -6.0) (<= (- t8 t5) -9.0))))
(assert (=> (and p_4_5 p_4_9) (or (<= (- t5 t9) -6.0) (<= (- t9 t5) -10.0))))
(assert (=> (and p_4_6 p_4_7) (or (<= (- t6 t7) -7.0) (<= (- t7 t6) -8.0))))
(assert (=> (and p_4_6 p_4_8) (or (<= (- t6 t8) -7.0) (<= (- t8 t6) -9.0))))
(assert (=> (and p_4_6 p_4_9) (or (<= (- t6 t9) -7.0) (<= (- t9 t6) -10.0))))
(assert (=> (and p_4_7 p_4_8) (or (<= (- t7 t8) -8.0) (<= (- t8 t7) -9.0))))
(assert (=> (and p_4_7 p_4_9) (or (<= (- t7 t9) -8.0) (<= (- t9 t7) -10.0))))
(assert (=> (and p_4_8 p_4_9) (or (<= (- t8 t9) -9.0) (<= (- t9 t8) -10.0))))
; jobs are limited by the global total duration time
(assert (<= t0 10.0))
(assert (<= t1 9.0))
(assert (<= t2 8.0))
(assert (<= t3 7.0))
(assert (<= t4 6.0))
(assert (<= t5 5.0))
(assert (<= t6 4.0))
(assert (<= t7 3.0))
(assert (<= t8 2.0))
(assert (<= t9 1.0))
(check-sat)
(exit)
