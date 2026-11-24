import YM.XSpace.Diastole
/-!
# Cooked symmetries prior to connected projection
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Rose
open Function Set Filter PowerSeries Structure1 Maxwell Maxwell.Free Maxwell.Wick Trace Graph3 Cirrus Normalize Retirement Photo Lattice
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}(W:Initialize G)(V: Normalize.Store G){n:ℕ}(d:ℕ)(x:Sample n)(p:Tags G d n)
lemma cooksR (e:ℕ)(p:Tags G d n): live W d x e (reel d ∘ p)= star (live W d x e p):=by
  let f:=chartV x; rw [live,lite,lite,star_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; let t (j:Fin n):HP G (i j).val:= Normalize.part d (i j) (p j); let s (j:Fin n):HP G (i j).val:=Normalize.part d (i j) (reel d (p j)); have he: W.atTuple x.F (fun j=>(i j).val) f s= PowerSeries.map (starRingEnd ℂ) (W.atTuple x.F (fun j=>(i j).val) f t):=by
    unfold t s; simp_rw [Initialize.atTuple_eq, fun j=> spoke (part_reel (p j) (i j).val) x.F W (f j), ← map_prod,Bare.normalize_real]; -- if type
  change coeff e (W.atTuple x.F _ _ s)=_; rw [he,coeff_map];rfl
lemma cookedR (e:ℕ)(p:Tags G d n): cooked W V d x e (reel d ∘ p)= star (cooked W V d x e p):=by
  rw [cooks,cooks,star_sum]; apply Finset.sum_congr rfl; intro i _; rw [← cooksR W d]; apply congr_arg; funext j; let l:= V.layout W (grab x) d (i (some j)); simp only [pulseU,comp_apply,decked,pulling]; split_ifs; exact (stood_reel ..).symm; exact l.property.2.2.1 _
lemma cooksO (e:ℕ): live W d x e (hinge d ∘ p)= ((-1:ℝ)^e) • live W d x e p:=by
  let f:=chartV x; rw [live,lite,lite,Finset.smul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; let t (j:Fin n):HP G (i j).val:= Normalize.part d (i j) (p j); let s (j:Fin n):HP G (i j).val:=Normalize.part d (i j) (hinge d (p j)); have he: W.atTuple x.F (fun j=>(i j).val) f s= rescale (-1:ℂ) (W.atTuple x.F (fun j=>(i j).val) f t):=by
    unfold t s; simp_rw [Initialize.atTuple_eq, fun j=> splinted (hinge_part (p j) (i j).val) x.F W (f j), ← map_prod,Bare.reverse_normalized]
  change coeff e (W.atTuple x.F _ _ s)= (-1:ℝ)^e • _; rw [he,coeff_rescale,Complex.real_smul,Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one]
lemma cooksV (e:ℕ)(H:V.Meets W x.F d): cooked W V d x e (hinge d ∘ p) = ((-1:ℝ)^e) • cooked W V d x e p:=by
  let A := V.layout W (grab x) d; have ht:faced A=A:= H.2.2.1; rw [cooks,cooks, Finset.smul_sum]; apply Finset.sum_congr rfl; intro i hi
  let a k:=(-1:ℝ)^k; let u j:= a (i (some j)); let v:=pulseU i (deck A) p; let y:= i none; let Q:=live W d x y
  rw [show pulseU i (deck A) (hinge d ∘ p)=fun j=> u j • hinge d (v j) from funext fun j=> by have hh:= posing A (i (some j)) (p j); rw [ht] at hh; exact hh]; change Q _= a e • Q v
  rw [show Q (fun j=> u j • hinge d (v j))=(∏ j,u j) • Q (hinge d ∘ v) from (Q.restrictScalars ℝ).map_smul_univ u (hinge d ∘ v),show Q (hinge d ∘ v)=a y • Q v from cooksO W d x v y, smul_smul]; have h:= (totaled i).mp hi; rw [Fintype.sum_option] at h; unfold u a y; rw [Finset.prod_pow_eq_pow_sum,mul_comm,← pow_add,h]
-- real profiles and cube deposit
variable {c:Shade.Cut}
def coerce (f: RealTest n): Test n where
 toFun:=fun x=> Complex.ofReal (f x)
 contDiff' := Complex.ofRealCLM.contDiff.comp f.contDiff
 hasCompactSupport':= f.hasCompactSupport.comp_left Complex.ofReal_zero
 tsupport_subset':= by rw [show tsupport (fun x=> (↑(f x):ℂ))=tsupport f by unfold tsupport; congr 1; ext1 i; simp]; exact f.tsupport_subset
end YM.XSpace.Rose
