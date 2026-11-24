import YM.AlbaMS.Loft.Roof

/-!
# Scale germs to vertices in perturbation algebra

Works at first in ℝ when scaling. Uses polynomial word powers one at a
time. No swap of scaling through arity in formal power series. Rank & locality
available through Loom. cohomogenic insertion scaling allowed different integer
weight. Heating introduced as canonically provided Jacobian, not a term
optional beyond free Action. Scale of commutator includes bracket zero mode.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric.Coil
open Finset Function Polynomial
open scoped BigOperators Classical Polynomial
variable {ι R S : Type*} [CommRing R][CommRing S]{ρ : ι→Bool} {p:Bool} {m n : ℕ}
variable {F G H J O : Coil ρ R} {g k : ι→ι→R}{s: Finset ι}(A:R→+* S)(z:R)
variable [Algebra ℚ R][Algebra ℚ S]

lemma halve_unique : A (halve R)=halve S:=by
  have he : A (halve R)+A (halve R)=halve S+ halve S:= by rw [halve_twice,← map_add, halve_twice,A.map_one]
  have hh (a:S): halve S*(a+a)=a:= by rw [mul_add, ← add_mul,halve_twice,one_mul]
  exact ((hh (A (halve R))).symm.trans ((congr_arg (fun y=>halve S*y) he).trans (hh _)))

-- master with independent delta-twist from origin; classical equation expressed as no-half form
structure Trad (F J:Coil ρ R)(g:ι→ι→R)(s:Finset ι) : Prop where
  tone : Tone false F
  dossier : Tone false J
  grow : needy 2 F
  bracket : cross true g s F F=0
  diff : cross true g s J J=0
  heat : touch g s F= -cross true g s F J
  touchJ : touch g s J=0
namespace Trad
variable (h : Trad F J g s)
include h
omit [Algebra ℚ R] [Algebra ℚ S] in
lemma scale : Trad (Wind _ A F) (Wind _ A J) (fun i j=>A (g i j)) s:= by

  exact { tone:= h.tone.seep _ _ _, dossier:= h.dossier.seep _ _ _, grow:= Wind_need _ _ h.grow, bracket:=by rw [← Wind_cross,h.bracket,map_zero], diff:=by rw [← Wind_cross,h.diff,map_zero], heat:=by rw [← Wind_touch,← Wind_cross,h.heat,map_neg], touchJ:=by rw [← Wind_touch,h.touchJ,map_zero] }
omit h [Algebra ℚ R] in
private lemma weave_touch : touch g s (weft (ρ:=ρ) (fun _=>z) G)=z^2 • weft (fun _=>z) (touch g s G):= weft_touch (fun _=>z) (fun _ _=>by ring) -- remove h
omit h [Algebra ℚ R] in
private lemma wmo (ht:Injective (fun x:R=>z^2*x)) : Injective (fun v:Coil ρ R=> z^2 • v) := fun _ _ he => ext _ _ fun l=> ht (DFunLike.congr_fun he l)
-- no analytic scaling: equality holds over Polynomial ring so remove nonzero factor
private lemma full (hv: Graded ρ true g)(ht:Injective (fun x:R=>z^2*x)): master g s (loom z 2 F - loom z 0 J)=0:=by
  let P:=loom z 2 F; let U:= loom z 0 J
  have he : z^2 • P=weft (fun _=>z) F:=(stride z 2 h.grow).symm
  have hu : U=weft (fun _=>z) J:=wefat _; change master g s (P-U)=0
  let T x y := cross true g s (x:Coil ρ R) y
  have hh X Y : T (weft (fun _=>z) X) (weft (fun _=>z) Y)= z^2 • weft (fun _=>z) (T X Y):= weft_cross (fun _=>z) (fun _ _=>by ring)
  have hH:Injective (fun (F : Coil ρ R)=> z^2 • F):=wmo z ht
  have h1:T P P=0:=by
    apply hH; apply hH; dsimp only [T]; rw [← smul_cross, ← cross_smul,he]; change T _ _=_; rw [hh,show T F F=0 from h.bracket, map_zero]; simp
  have h2:T U U=0:=by rw [hu,hh]; rw [show T J J=0 from h.diff,map_zero,smul_zero]
  have h3:T P U=weft (fun _=>z) (T F J):=by apply hH; change z^2 • cross true _ _ _ _=_; rw [← smul_cross,he,hu]; exact hh F J
  have h4 : touch g s P= -T P U:= by
    rw [h3,← map_neg,← show touch g s F=_ from h.heat]; apply hH; change z^2 • touch g s P=_; rw [← map_smul,he,weave_touch z]
  have h5 : touch g s U=0:= by rw [hu,weave_touch z,h.touchJ,map_zero,smul_zero]
  have h6:T U P=T P U:= cross_flip (h.dossier.loom z 0) (h.tone.loom z 2) hv
  have hg:tether true g s (P-U) (P-U)= -(T P U+T P U):=by
    simp only [map_sub,LinearMap.sub_apply,from_tether]; change T P P-T U P-(T P U-T U U)=_; rw [h1,h2,h6]; abel
  rw [master,map_sub,h5,← from_tether,hg,smul_neg,twice_halve,h4]; simp
lemma heatproof [IsDomain R] (hv: Graded ρ true g)(b:S): master (fun i j=>A (g i j)) s (loom b 2 (Wind _ A F)-loom b 0 (Wind _ A J))=0:=by
  -- even if b is nilpotent. Eval from R[X]. Monic X.
  let L:= eval₂RingHom A b
  let K:= fun i j=> C (g i j); let Δ : Trad (Wind _ C F) (Wind _ C J) K s:=scale (Polynomial.C) h
  have hp:Graded ρ true K:= fun i j hh=> hv i j fun hu=> hh (by simp [K,hu]);
  have ht : Injective (fun y:R[X]=> X^2*y):=mul_right_injective₀ (pow_ne_zero _ X_ne_zero)
  have hh:= congr_arg (Wind ρ L) (full X Δ hp ht); unfold master at hh ⊢
  simp_rw [map_sub,map_zero (Wind _ _),Wind_smul,Wind_cross, Wind_touch] at hh -- repeat map_sub
  have he:∀ U:Coil ρ R, Wind _ L (Wind _ C U)= Wind _ A U:= by intro v; ext l; simp_rw [blows,seep_read]; change L (C _)= A _; simp [L]
  simp_rw [halve_unique (R:=R[X]),map_sub, loom_map X _ L, show L X=b from by simp [L],he, show ∀ i j,L (K i j)=A (g i j) from fun i j=> by simp [K,L]] at hh
  simpa only [map_sub] using hh
end Trad
end YM.MSBar.Bric.Coil

namespace YM.MSBar.Loft
open Finset Function Bric Coil
open scoped BigOperators Classical
variable {E B R S : Type*}[Fintype E][Fintype B][CommRing R][CommRing S]{g k : Place E B→Place E B→R}{F J : Floor E B R}
lemma Under.delta (h:Under F) : Loft.delta F=0:=by simp_rw [dots,h.1,h.2]; simp
lemma Under.free (ht:EvenT F)(h:Under F)(H:Under J): coupling F J=0:=by simp_rw [connects _ _ ht, h.1,h.2,H.1,H.2]; simp
variable [Algebra ℚ R] {M: Codes B R}{z:B→E→Floor E B R}
namespace Panel
variable (h:Panel M z F J)
include h
lemma keep (hv:needy 2 (superb M z F)): Trad (superb M z F) J (oriented R) Finset.univ:= by
  -- trick top bracket zero despite 1/2
  refine ⟨h.tone, h.evenJ,hv,?_, h.simpleJ.1.free h.evenJ h.simpleJ.1, h.height, h.simpleJ.1.delta⟩ -- order args free
  let Y:= superb M z F; let Q := coupling Y Y; change Q=0; rw [← twice_halve Q,smul_add, show halve R • Q=0 from h.top,add_zero]
end Panel
end YM.MSBar.Loft
