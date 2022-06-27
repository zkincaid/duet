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
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (let ((?v_0 (* skoC (/ 1770 689)))) (and (not (<= (* skoX (+ (/ (- 128421199872) 390625) (* skoX (+ (/ 48157949952 1220703125) (* skoX (+ (/ (- 12039487488) 3814697265625) (* skoX (+ (/ 2222131968 11920928955078125) (* skoX (+ (/ (- 317447424) 37252902984619140625) (* skoX (+ (/ 35960841 116415321826934814453125) (* skoX (+ (/ (- 26040609) 2910383045673370361328125000) (* skoX (+ (/ 479891223 2328306436538696289062500000000000) (* skoX (+ (/ (- 107882523) 29103830456733703613281250000000000000) (* skoX (+ (/ 145083393 2910383045673370361328125000000000000000000) (* skoX (+ (/ (- 33480783) 72759576141834259033203125000000000000000000000) (* skoX (/ 33480783 14551915228366851806640625000000000000000000000000000)))))))))))))))))))))))) (/ (- 171228266496) 125))) (and (not (<= skoX 0)) (or (not (<= ?v_0 skoS)) (not (<= skoS ?v_0)))))))
(check-sat)
(exit)
