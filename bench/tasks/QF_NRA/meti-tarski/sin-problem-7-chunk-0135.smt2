(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The meti-tarski benchmarks are proof obligations extracted from the
Meti-Tarski project, see:

  B. Akbarpour and L. C. Paulson. MetiTarski: An automatic theorem prover
  for real-valued special functions. Journal of Automated Reasoning,
  44(3):175-205, 2010.

Submitted by Dejan Jovanovic for SMT-LIB.


|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* skoY (* skoX (* skoX (+ (/ 1 6) (* skoX (* skoX (+ (/ (- 1) 120) (* skoX (* skoX (/ 1 5040)))))))))) 0)) (and (not (<= (* skoY (* skoY (+ (* skoX (/ (- 1) 6)) (* skoY (* skoY (* skoX (/ 1 120))))))) (* skoX (* skoX (* skoX (+ (/ (- 1) 6) (* skoX (* skoX (+ (/ 1 120) (* skoX (* skoX (/ (- 1) 5040)))))))))))) (and (not (<= (* skoY (+ (* skoX (* skoX (/ 1 6))) (* skoY (* skoY (+ (/ (- 1) 6) (* skoY (* skoY (/ 1 120)))))))) 0)) (and (not (<= skoX 0)) (and (not (<= pi (/ 15707963 5000000))) (and (not (<= (/ 31415927 10000000) pi)) (and (<= skoY (* pi (/ 1 2))) (and (<= 0 skoX) (not (<= skoY skoX)))))))))))
(check-sat)
(exit)
