gap> n := 4;; q := 3;; s := 2;;
gap> G := GammaLMeetSL(n, q, s);;
gap> Size(G) = Size(SL(n / s, q ^ s)) * (q ^ s - 1) / (q - 1) * s;
true
gap> n := 2;; q := 2;; s := 2;;
gap> G := GammaLMeetSL(n, q, s);;
gap> Size(G) = Size(SL(n / s, q ^ s)) * (q ^ s - 1) / (q - 1) * s;
true
gap> n := 6;; q := 5;; s := 6;;
gap> G := GammaLMeetSL(n, q, s);;
gap> Size(G) = Size(SL(n / s, q ^ s)) * (q ^ s - 1) / (q - 1) * s;
true
gap> n := 6;; q := 4;; s := 2;;
gap> G := GammaLMeetSL(n, q, s);;
gap> Size(G) = Size(SL(n / s, q ^ s)) * (q ^ s - 1) / (q - 1) * s;
true
