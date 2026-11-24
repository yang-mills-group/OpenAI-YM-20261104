import YM.MS.Local.Labels
import YM.Maxwell.Equation
/-!
# Testing the covector of an actual Taylor jet on a plane wave

The MS labels use the free homogeneous-row quotient. We want to identify them with the
Taylor labels of the manuscript and existence theorem, eventually on shell. Before any
quotient develop a pairing with unconstrained Symbol.Fibre. Note factorial normalization for
repeated ordinary derivatives. Four-dimensional coefficient metric exactly as in G.Color.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Theater
open Set Function Filter Finset Metric MeasureTheory Real Submodule
open Analysis Tensor Koszul Plane Landau Detect
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {J E K:Type} [Fintype J]{G:Gauge}{h i r n:ℕ}
  [NormedAddCommGroup E][NormedSpace ℝ E]
-- use Sym, not assume directional slash.C.L.
def DeckC (J:Type)(G:Gauge)(h:ℕ): Submodule ℝ ( J→ Tensor.T E4 G.Color h ):={
   carrier:={F | ∀ i: J, Tensor.Sym (F i)}
   zero_mem':=fun _ _ _=> rfl
   add_mem':=fun hx ht i s p=>by simp [hx i s p, ht i s p]; -- shape care elaboration
   smul_mem':=fun a x h i s p=>by simp [h i s p] }
abbrev LightC (J:Type)(G:Gauge)(h:ℕ) := ↥( DeckC J G h )
-- tensors on a real input $E$, work with powers only for Jet read. value at E4 via dense pairing basis.
abbrev amount (j:ℕ):ℝ:= ( Nat.factorial j:ℝ )⁻¹
lemma amt_p (j:ℕ): 0<amount j:= by unfold amount; positivity
lemma periodC (i:ℕ): (i+1:ℝ)*amount (i+1)=amount i:= by unfold amount; rw [ Nat.factorial_succ ]; push_cast; field_simp
open InnerProductSpace
local notation "tP"=> Fin
abbrev lampC (h:ℕ)(p:E4) (v:G.Color): Tensor.T E4 G.Color h:= (ContinuousMultilinearMap.mkPiRing ℝ ( Fin h ) v).compContinuousLinearMap (fun _=> innerSL ℝ p)
lemma pulse (v:G.Color)(q: Fin n→ E4)(p:E4): lampC n p v q=(∏ i,inner ℝ p ( q i )) • v:= by simp [lampC] -- $lemma
lemma lamp_symC (h:ℕ)(v:G.Color)(p:E4): Tensor.Sym (lampC h p v):= by
    intro s p'; rw [pulse,pulse]; exact congr_arg (· • v) (Equiv.prod_comp p' (fun i=>inner ℝ p ( s i )))
omit [Fintype J] in
open Classical in -- syntax local?
def planeC (t:J) (h:ℕ)(p:E4)(v:G.Color): LightC J G h:= amount h • ( ⟨ fun i=> if i=t then lampC h p v else 0,fun i s r=> by dsimp only; split; exact lamp_symC h v p s r; rfl ⟩ : LightC J G h )
omit [Fintype J] in
lemma wearing (t:J)(p:E4)(v:G.Color)(q: Fin h→ E4): ( planeC t h p v ).val t q= amount h • ((∏ i,inner ℝ p ( q i )) • v):= by classical unfold planeC; simp only [Submodule.coe_smul,Pi.smul_apply,if_true, smul_apply,pulse] -- just
omit [Fintype J] in
lemma away {t i:J}(h:ℕ)(p:E4)(v:G.Color)(ht:i≠t): ( planeC t h p v ).val i=0:= by unfold planeC; simp only [Submodule.coe_smul,Pi.smul_apply]; rw [if_neg ht,smul_zero]
-- Riesz pairing.
open Tensor
abbrev Fill (f:Fin h→Axis): Fin h→E4:= basis∘ f
def ticket (J:Type)[Fintype J](G:Gauge)(h:ℕ): LightC J G h →ₗ[ℝ] LightC J G h →ₗ[ℝ] ℝ := {
  toFun x := { toFun u:= ∑ i:J,∑ j:Fin h→Axis,inner ℝ ( x.val i ( Fill j )) (u.val i ( Fill j )), map_add' a b:= by simp [inner_add_right,Finset.sum_add_distrib], map_smul' a b:= by simp [inner_smul_right, Finset.mul_sum] }
  map_add' a b:= by apply LinearMap.ext; intro x; simp [inner_add_left,Finset.sum_add_distrib]
  map_smul' a b:= by apply LinearMap.ext; intro x; simp [inner_smul_left, Finset.mul_sum] }
local notation "γ"=> ticket J G h
-- tensor expansion in axis directions
lemma exprY (F:Tensor.T E4 E h)(p:E4): diagonal F p= ∑ j: Fin h→ Axis,(∏ i, p ( j i )) • F ( Fill j ):= by
    obtain he: ∑ i:Axis, p i • basis i=p:= by ext i; simp
    let M:=F.toMultilinearMap; have hh : diagonal F p= M fun _=>∑ i:Axis,p i • basis i:= by rw [he]; rfl
    rw [ hh, M.map_sum ]; exact Finset.sum_congr rfl fun j _=> M.map_smul_univ (fun i=> p (j i)) _
lemma ticketPlane (X:LightC J G h)(t:J)(v:G.Color)(p:E4): γ X ( planeC t h p v )= amount h * (inner ℝ ( diagonal ( X.val t ) p ) v):= by
   classical
   unfold ticket; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [Finset.sum_eq_single_of_mem t ( Finset.mem_univ t ) ]; · rw [exprY, sum_inner, Finset.mul_sum ]; simp_rw [ wearing, inner_smul_right, inner_smul_left ]; refine Finset.sum_congr rfl fun i _=> ?_; simp [ Fill ]; left; left; apply Finset.prod_congr rfl; intro j hj; exact Eq.trans (real_inner_comm _ p) (basis_inner (i j) p)
   intro i hi ht; rw [away h p v ht]; simp
-- determine.X
omit [Fintype J] in
lemma absolute (X:LightC J G h)(hc:∀ i: J,∀ p:E4,diagonal ( X.val i ) p=0): X=0 := by
    apply Subtype.ext; ext1 i; apply Tensor.ext_diag; · exact X.property i
    · exact fun _ _=> rfl
    exact funext fun p=> hc i p
abbrev cl (G:Gauge)(i:G.ColorIndex): G.Color:= EuclideanSpace.single i 1
lemma pigment (i:G.ColorIndex)(x:G.Color): inner ℝ x (cl G i)=x i:= by classical unfold cl; rw [ EuclideanSpace.inner_single_right ]; simp
lemma excerpt (X:LightC J G h)(t:J)(i:G.ColorIndex)(p:E4): γ X (planeC t h p ( cl G i )) = amount h * diagonal ( X.val t ) p i := by rw [ticketPlane,pigment]
lemma seat_inj : Injective γ:= by
   apply LinearMap.ker_eq_bot.mp; apply eq_bot_iff.mpr; intro x hx; have hu: γ x=0:=LinearMap.mem_ker.mp hx; refine (Submodule.mem_bot _).mpr (absolute _ (fun i p=>?_)); ext k; obtain he := excerpt x i k p; rw [hu] at he; exact (mul_eq_zero.mp (show amount h * _=0 from he.symm)).resolve_left (amt_p h).ne' -- ambiguity
lemma seat_surj : Surjective γ:= by apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp seat_inj; exact (Subspace.dual_finrank_eq ..).symm
-- all support.Span use ordinary.P
lemma termsTop : Submodule.span ℝ {x:LightC J G h|∃ i:J,∃ k:G.ColorIndex,∃ p:E4, x=planeC i h p (cl G k)}=⊤:= by
    let V : Submodule ℝ (LightC J G h) := Submodule.span ℝ {x:LightC J G h|∃ i:J,∃ k:G.ColorIndex,∃ p:E4, x=planeC i h p (cl G k)}; change V = ⊤; apply Submodule.dualAnnihilator_eq_bot_iff.mp; apply eq_bot_iff.mpr; intro p hp; obtain ⟨x,rfl⟩:= seat_surj p; have hz: x=0:= by
       refine absolute x fun i v=> ?_; ext k; obtain ht:= excerpt x i k v; rw [Submodule.mem_dualAnnihilator] at hp; rw [ hp (planeC i h v (cl G k)) (by apply Submodule.subset_span; exact ⟨i,k,v,rfl⟩) ] at ht; exact (mul_eq_zero.mp ht.symm).resolve_left (amt_p h).ne'
    rw [hz,map_zero]; exact (⊥:Submodule ℝ _).zero_mem
end YM.MS.Theater
