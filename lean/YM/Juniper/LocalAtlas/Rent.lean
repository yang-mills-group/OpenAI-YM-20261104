import YM.Juniper.LocalAtlas.Law
/-!
 # Rate G L invoice

 Here choose p-order n marker corner. For final quote $W$ in g schedule,
 display loss ($7/8 (n+1)$) from all y in WHOLE eaves. To improve θ region
 to y of actual smaller size, retain b-scaled version: no-cost `≠eta*N`
 loss after evaluating on reachable stronger field. Or compute enough extra
 internal orders and use coefficient caps in smaller region.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Juniper.LocalAtlas
open Filter Set Function Metric ProbabilityTheory MeasureTheory Matrix
open PhysicalNext.Repeat Lantern Sienna
open Lattice RG Wilson Pressure Push Push.AbsoluteSums
open ConnectedActivityE6 Blaze Brush Poll Coat
open scoped Topology ContDiff BigOperators Classical MatrixOrder
variable {G : Gauge} {L : Side}

section revenue
local notation "r!"=> Rate G L
variable (d : ℝ) (D A : ℝ→ℝ)(W X c:ℝ)(n k:ℕ){s : ℝ} {f g t p q:ℝ→ℝ}
private lemma mul_zeroR (h : r! s f)(he:r! 0 g): r! s (fun t=> f t*g t):= by simpa only [add_zero] using h.mul he
private lemma zeroR_mul (he:r! 0 f)(h:r! s g): r! s (fun t=> f t*g t):= by simpa only [zero_add] using he.mul h
local notation "P" => betaF G
private lemma gamut_rate (Q : ℝ →ℝ)(h : Rate G L 0 Q): Rate G L 0 (fun t=> gamut (Q t) c k):= Brim.bell (Brim.prep ((Rate.const 1).add h) k) ((Rate.const 1).add (Rate.mul_right h _))
variable {A D}(h : Rate G L 0 A)(hp : Rate G L 0 p)(ht : Rate G L 0 D)
include hp ht
private lemma base_rate : Rate G L 0 (fun t=> baseW (D t) W (p t) k):= lumpRate k (fareRate k hp ht) (Rate.const _)
private lemma principal_rate : Rate G L 0 (fun t=> preAux k (p t) (D t) W) := by
  let B y:= acrossE k (p y) (D y); let b:= fun t=>spanE (p t) (D t)
  have hz:= ((Rate.const 1).add hp).add ht
  have hb : r! 0 b:= hz.add hz
  have hx : Rate G L 0 B := Brim.bell ht (Brim.bell ht (lumpRate k hb hp))
  exact lumpRate k ((fareRate k hp ht).add (hx.mul_left _)) (Rate.const _)
include h
private lemma XTag_rate : Rate G L 0 (fun t=>XTag (D t) W (p t) (A t) c n k) := (Brim.bell (principal_rate W k hp ht) (gamut_rate c _ A h)).mul_left (overhead ..)
private lemma loss_rate (f:ℝ→ℝ) (hF:r! s f) (hR:∀ᶠ x in atTop,0 < f x) : Rate G L s (fun t=> debt₀ (D t) W (p t) (A t) c (f t) ((f t)^2) k):= by
  have he : Rate G L s (fun t=> (f t)^2 * (f t)⁻¹) := hF.congr (hR.mono fun x hx=> (by field_simp))
  exact zeroR_mul (principal_rate W k hp ht) ((mul_zeroR hF (gamut_rate c _ A h)).add he)

def scoop (G:Gauge)(L:Side)(n:ℕ)(x:ℝ):= eaves G L x^(n+1)
def leaf (n:ℕ): ℝ:=vow*(n+1:ℕ)
local notation "ℓ"=> leaf n
local notation "Φ"=> eaves G L
local notation "N"=> scoop G L n
omit hp ht h
private lemma basepow : scoop G L n =ᶠ[atTop] fun x=> P x L ^ℓ:=by
    filter_upwards [Delay.shift_pos G L] with x hx; exact Eq.symm ((Real.rpow_mul (show 0≤ P x L from hx.le) vow ((n+1:ℕ):ℝ)).trans (Real.rpow_natCast _ (n+1)))
lemma leaf_neg : leaf n <0:= mul_neg_of_neg_of_pos vow_ok (by exact_mod_cast (Nat.succ_pos n))
lemma pos : ∀ᶠ x in atTop,0 < scoop G L n x:= (Delay.shift_pos G L).mono fun _ h=>pow_pos (Real.rpow_pos_of_pos h _) _
include hp ht h
private lemma rat_net : Rate G L (leaf n) (fun t=> net (D t) W (p t) (A t) c (N t) ((N t)^2) (Φ t) n k):= by
    let u:= fun x=> baseW (D x) W (p x) k; have hU:r! 0 u:= base_rate W k hp ht
    have hq : Rate G L (leaf n) (fun t=>scoop G L n t):= (edge G L).pow (n+1)
    exact (zeroR_mul (hU.add (hU.mul_left _)) hq).add ((loss_rate W c k h hp ht N hq (pos n)).mul_left _)
private lemma price_rate : Rate G L (leaf n) (fun t=>value (D t) W (p t) X (A t) c (N t) ((N t)^2) (Φ t) n k):=by
    let S:= fun x=> clump k (XTag (D x) W (p x) (A x) c n k) X
    have hX:= XTag_rate W c n k h hp ht; have hs : r! 0 S:= lumpRate k hX (Rate.const _)
    have hf:= rat_net W c n k h hp ht
    exact ((mul_zeroR hf (lumpRate k (((base_rate W k hp ht).add hX).mul_left 2) (Rate.const _))).mul_left _).add (zeroR_mul (hs.add (hs.mul_left _)) ((edge G L).pow (n+1)))

omit ht
lemma rate_log (hd : 0 < d)(I : Lantern.Bolt G L A)(hc: 0 < c)(hk:n+1 ≤ k) (D':ℝ) (hD:leaf n < D') :
    ∃ S W:ℝ→ℝ, Rate G L 0 S ∧ Rate G L 0 W ∧ ∀ᶠ t in atTop,
      let x:= betaF G t L; let D:= wick G L d t; let u:= eaves G L t; let w:= S t; let v:= W t
      ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
      (ι : Type)[Fintype ι][DecidableEq ι] (φ ψ : E × Poll.Body ι → ℝ)(ρ:E → Poll.Body ι) (M:E→ Matrix ι ι ℝ),
      (Fintype.card ι:ℝ) ≤ A t → (H : Golf φ ψ ρ M k D u u (p t)) →
      (∀ z:ι→ℝ,dotProduct z ((M 0)⁻¹ *ᵥ z) ≤ c*dotProduct z z) → ∀ y:ℝ×E, ‖y‖<u→
      Brush k w 1 (through n (oneEra φ ψ ρ M)) y ∧
      Brush k v 1 (Real.log ∘ through n (oneEra φ ψ ρ M)) y ∧
      Brush k (x^D') u⁻¹ (cleanLog φ ψ ρ M D-cleanLetter φ ψ ρ M n) y := by
   let D t:= wick G L d t; have hq : r! 0 D:= gen G L d
   let e:ℝ:= Real.exp (-1)*(1/2)/2
   obtain ⟨T,hT,hT'⟩:=Brush.compact (f:=Real.exp) (k:=k) isCompact_Icc fun x (_:x∈Icc (-1:ℝ) 1)=> Real.contDiff_exp.contDiffAt
   obtain ⟨U,-,hU⟩:= treasury k e (Real.exp 1+e) (by positivity)
   let S t:=XTag (D t) T (p t) (A t) c n k
   have hs : r! 0 S:= XTag_rate _ c n k h hp hq
   let hP := (edge G L).pow (n+1)
   have hr := walls G L I hc hd (2*leaf n)
   have he := (hP.pow 2).below (mul_neg_of_neg_of_pos (leaf_neg n) (by positivity : (0:ℝ)< (2:ℕ))) (1/2:ℝ) (by norm_num)
   have hx:∀ᶠ t in atTop,1 ≤ D t:=by
     filter_upwards [ (Bolt.still (G:=G) (L:=L) (1/d)).listens zero_lt_one ] with t ht
     rw [Real.rpow_one] at ht; exact ((div_le_iff₀ hd).mp ((le_abs_self _).trans ht)).trans_eq (mul_comm ..)
   have hy:= (mul_zeroR (edge G L) (fareRate k hp hq)).below vow_ok _ zero_lt_one
   refine ⟨S,fun x=> clump k (S x) U,hs, lumpRate k hs (Rate.const _),?_⟩
   filter_upwards [(price_rate T U c n k h hp hq) D' hD, he,hx,hy,hr,basepow n (G:=G) (L:=L),pos n (G:=G) (L:=L),
      Delay.shift_pos G L,(rat_net T c n k h hp hq).below (leaf_neg n) e (by positivity)] with t hd' he hD hy hr hN hx hz hw x D' u w v E _ _ _ ι _ _ φ ψ ρ M hA H hf y ht
   let A':= A t; let Q':= N t; let f:= p t
   have H' : Wager D' u T U A' f ((Q':ℝ)^ (2:ℕ)) Q' c n k := ⟨hD, (mul_comm ..).trans_le ((le_abs_self _).trans hy), hT',hU,hx,(le_abs_self _).trans he, (le_abs_self _).trans hw⟩
   have he: ‖(0:E)‖<u:=by rw [norm_zero]; exact H.pos
   let μ := sweep (M 0)⁻¹
   have ht' : μ.real (closedBall (0:Poll.Body ι) D')ᶜ ≤ Q'^ (2:ℕ):=by
     rw [measureReal_compl measurableSet_closedBall, probReal_univ]; refine (hr _ _ hA (H.gram _ he).1.inv hf).trans ?_
     unfold Q'; rw [hN,mul_comm 2,Real.rpow_mul (by positivity)]; norm_cast -- cast
   refine ⟨gross _ (fun i hi=> (coin_limit H H'.born hf hT' i (hi.trans (by omega)) hA).2) (ht.le.trans H.small) _, (rising hk H hf H' ht' hA ht).2.2.2, (fit hk H hf H' ht' hA ht).climb ((le_abs_self _).trans hd') le_rfl⟩
end revenue
end YM.Juniper.LocalAtlas
