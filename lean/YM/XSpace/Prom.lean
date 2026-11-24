import YM.XSpace.PrismLeg
/-! # Slot pricing and literal top first correction -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Chiral
open Function Set Filter Lattice Trace Chart2 Maxwell Maxwell.Free Structure1 Normalize Source Source.Drops Wilson Stall Labels MvPolynomial Pages RG Contraction Next.Rank.Normal Finsupp Mu
open scoped Topology BigOperators InnerProductSpace Classical
variable {G:Gauge}{d n:ℕ}{H:Hol G}(h:G.Simple)(S:Survey G H d)(x:Cover)
abbrev P0 := Encore.reel S x
def P1: Labels.Pol G →ₗ[ℂ] Stamp G:= (PowerSeries.coeff (R:=Stamp G) 1).restrictScalars ℂ ∘ₗ (toy S x).toLinearMap
lemma π1 (p:Labels.Pol G): P1 S x p=p1 S x p:=rfl
lemma π0 (p:Labels.Pol G): P0 S x p=p0 S x p:=(Encore.tuned ..).symm
lemma stimulated (p q:Labels.Pol G): P1 S x (p*q)=P1 S x p * P0 S x q+ P0 S x p * P1 S x q:=by rw [π0,π0]; unfold P1 p0; simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,LinearMap.restrictScalars_apply,map_mul,PowerSeries.coeff_one_mul]; ring
lemma strongs (L:Line G): Hom (harp L) 1:=by refine glow ?_; intro t B; rw [leg_test,leg_test,map_smul,smul_eq_mul,smul_eq_mul,Complex.ofReal_mul,pow_one]
lemma P0_bound {p:Labels.Pol G}(h:p∈DegZ (Labels.Key G) n): P0 S x p∈ DegZ (UnitIndex G) n:=by apply sustains _ h; intro i; unfold P0 Encore.reel; rw [exchange_x]; exact hom_g (strongs (G:=G) (displace _ (ping ..)))
lemma P1_X (i: Labels.Key G) : Hom (P1 S x (MvPolynomial.X i)) 2:=by
  rw [π1,p1,toy,aeval_X, coefficient_knit]; refine glow ?_; intro t A; rw [pit_right,pit_right,second_fee,map_smul, Complex.real_smul,Complex.ofReal_pow,smul_eq_mul]
lemma P1_bound {p:Labels.Pol G}(h:p∈DegZ (Labels.Key G) n): P1 S x p∈ DegZ (UnitIndex G) (n+1):=by
  have he (r:Labels.Key G→₀ ℕ)(c:ℂ): P1 S x (monomial r c) ∈ DegZ (UnitIndex G) (Volume r+1):=by
    apply Extra.FD.per_factor r; simp [P1,toy, PowerSeries.algebraMap_apply,MvPolynomial.algebraMap_eq]
    intro s i hs; rw [monomial_add_single,pow_one,volume_fee,stimulated]; apply Submodule.add_mem; exact bounds_mul _ hs (P0_bound S x (hom_g (isWeightedHomogeneous_X ..))); rw [add_assoc (Volume _ )]; exact bounds_mul _ (P0_bound S x (hom_g (home_m s c))) (hom_g (P1_X ..))
  rw [p.as_sum,map_sum]; exact Submodule.sum_mem _ fun i hi=> higher _ (Nat.add_le_add_right ((bounded _).1 h _ hi) 1) (he ..)

lemma price_field (p:Sec G d): p.val∈DegZ (Maxwell.Slot G) (d/2):=by
  rw [bounded]; intro i hi; let he : ↥(lowerCap G d):= ⟨p.val,(sector.mp p.property).1⟩ -- context
  have hx : weight scaleW i ≤ d:= (bounded _).1 (show p.val∈lowerCap G d from he.property) i hi
  have hh : ∀ i:Maxwell.Slot G→₀ℕ,Volume i + Volume i ≤ weight scaleW i:=by
    intro i; apply Extra.FD.per_factor i; · simp
    intro s i h; rw [volume_fee,map_add,weight_single,one_smul]; rw [show scaleW (G:=G) i=i.1+2 from rfl]; omega
  specialize hh i; change Volume i ≤ _; omega
lemma P0_cap (W:Initialize G)(p:Sec G d): Bracket.screenplay W d p∈ DegZ (UnitIndex G) (d/2):=by
  have ht {k:ℕ}(p: On.Grade G k): Prelude.enter0 (W.surveys k) p∈ DegZ (UnitIndex G) (k/2):=by
    unfold Prelude.enter0; rw [Price.preparedV]; exact P0_bound _ _ (Stall.sustains (fun i=>hom_g (On.grade (fun _=>(1:ℕ)) i)) (price_field (en le_rfl p)))
  rw [Bracket.screen]; apply Submodule.sum_mem; intro i _; apply higher _ _ (ht (Normalize.part d (i:ℕ) p)); have h:=i.isLt; omega

lemma upgraded (q:HP G d)(h:q.val∈DegZ (Maxwell.Slot G) (n+1)):
 Trace.volume x (Prelude.mark1 S q)- P1 S x (On.lifting q.val)∈ DegZ (UnitIndex G) (n+1):=by
  let Q:=On.lifting q.val; let p:= milk (S.selfCov (-1)) Q; have hh : Q∈DegZ (Labels.Key G) (n+1):= sustains (fun i=>hom_g (On.grade (fun _=>(1:ℕ)) i)) h; have ht:p-Q∈DegZ (Labels.Key G) n:=ward_limit _ _ hh
  have he: Trace.volume x (Prelude.mark1 S q)= flicker (P1 S x p):= by
    unfold Prelude.mark1; rw [Prelude.startField,Survey.insertW_val,Price.preparedV,π1, ← show ∀ p, flicker (Trace.volume (G:=G) x p)=Trace.volume x (flicker p) from fun p=>meant x p,Trace.stained (G:=G),Outline.Chart.pull1]; simp [Outline.Chart.lug]; rfl
  rw [he,← sub_add_sub_cancel (flicker _) (P1 S x p) _]; apply Submodule.add_mem; exact ward_limit (Mu.root G) _ (P1_bound S x (wick_bound _ _ hh)); rw [← map_sub]; exact P1_bound _ x ht
end YM.XSpace.Chiral
