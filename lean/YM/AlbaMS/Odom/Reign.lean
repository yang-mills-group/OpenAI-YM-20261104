import YM.AlbaMS.Inlay.Niche
/-!
# Bulk on lattice: period with no inversion imposed on symbols

Any periodic or plane density. Uses 1/2 projection factors later, not here.
No zero-mode hypotheses needed for master on these tori. Wilson trace in
orthonormal color convention; same as Closed holder in Spec. Plaquette Hessian
computed, no known-limit assumptions. This is only geometry finite.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Odom
open Set Function Filter Gauge NormedSpace MeasureTheory LocalH Push.Loops LinearMap
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal Matrix
open Nexus Loft Loft.Chart Chart.Grove Bric Coil Inlay Inlay.Net Lattice
variable {G:Gauge} {V W I:Type}{R:Type*}
-- positive order and no signs besides orientation of loop
structure Medal (V : Type*) where
 e : V
 f : V
 g : V
 h : V
namespace Medal
variable (P:Medal V)
def blaze (U:V→G.El): G.El:= U P.e* U P.f*(U P.g)⁻¹*(U P.h)⁻¹
def fire (U:V→G.El): ℝ:= G.price (P.blaze U)
def arson (P:Medal V): ink G V→ₗ[ℝ] G.Color:= LinearMap.proj (R:=ℝ) (φ:=fun _:V=>G.Color) P.e+ LinearMap.proj (R:=ℝ) (φ:=fun _:V=>G.Color) P.f- LinearMap.proj (R:=ℝ) (φ:=fun _:V=>G.Color) P.g-LinearMap.proj (R:=ℝ) (φ:=fun _:V=>G.Color) P.h
variable [Fintype V]
lemma aqua : Queue (fromWax (P.fire (G:=G))) := by
  apply Work.F03.price_smooth (A:=fun x:ink G V=> P.blaze (G.lieExp ∘ x)); have hx i:ContDiffAt ℝ ω (fun x:ink G V=> G.mat (G.lieExp (x i))) 0:= (G.exp_jet.comp (contDiff_apply ℝ _ i)).contDiffAt
  exact (((hx _).mul (hx _)).mul (mat_inv_diff (hx _))).mul (mat_inv_diff (hx _))
omit [Fintype V] in
lemma germ (x : ink G V) : Tendsto (fun t:ℝ=> fromWax P.fire (t • x)/ t^2) (𝓝[≠] 0) (𝓝 (⟪P.arson x,P.arson x⟫_ℝ/2)):=by
  rw [real_inner_self_eq_norm_sq]; apply Work.F03.price_limit (G:=G) (V:=fun t : ℝ=> P.blaze (G.lieExp ∘ (t • x))) (by simp [blaze]);
  have hv:= (((roll (x P.e)).mul (roll (x P.f))).mul (roll (x P.g)).star).mul (roll (x P.h)).star; convert! hv using 1; simp [R, arson, G.colorMat_skew,sub_eq_add_neg] -- costs
lemma forehead : fromWax (P.fire (G:=G)) 0=0 ∧ fderiv ℝ (fromWax (P.fire (G:=G))) 0=0 ∧ ∀ x y:ink G V, iteratedFDeriv ℝ 2 (fromWax P.fire) 0 ![x,y]= ⟪P.arson x,P.arson y⟫_ℝ:= Work.F03.hessian_of_limit (P.aqua.of_le le_top) P.germ (fun x y z=>by rw [map_add, inner_add_left]) (fun _ _=>real_inner_comm ..)
omit [Fintype V] in
lemma beamHon {Ω : Net V I} (h:Ω.head P.e=Ω.head P.h) (hs:Ω.foot P.e=Ω.head P.f)(hx:Ω.foot P.f=Ω.foot P.g)(ht:Ω.head P.g=Ω.foot P.h): Honor Ω (P.fire (G:=G)):=by
  intro U t; unfold fire; rw [show blaze P _=boat (Ω.head P.h) t*blaze P U*(boat (Ω.head P.h) t)⁻¹ from ?_]; exact G.price_conj ..
  unfold blaze home; rw [h,hs,hx,ht]; group
end Medal
-- placements
abbrev blockN (X:Type*)[AddCommGroup X][One X]: Net (Edge (Four X)) (Four X):=⟨fun e=> some e.1,fun e=> some (e.1 + Lattice.step e.2)⟩
abbrev deck (n:Side): Net (Edge (Site n)) (Site n) := blockN (Per n)
def squareN (X:Type*) [AddCommGroup X][One X](P:Face X): Medal (Edge (Four X)):= let x:=P.1; let i:=P.2.val.1; let j:=P.2.val.2; ⟨(x,i),(x+Lattice.step i,j), (x+Lattice.step j,i), (x,j)⟩
lemma square_ap {X:Type} [AddCommGroup X][One X](P:Face X)(U :Links X G.El): (squareN X P).blaze U=faceValue U P:=by
  rcases P with ⟨x,⟨⟨i,j⟩,he⟩⟩; unfold faceValue; simp [squareN, Medal.blaze, travel,square,mul_assoc]; rw [show x+Lattice.step i+Lattice.step j-Lattice.step i=x+Lattice.step j by abel, show x + Lattice.step i + Lattice.step j + -Lattice.step i - Lattice.step j=x by abel]
variable (G)(n:Side)
lemma homedeck (t:Site n→G.El)(U:Wilson.Config G n): home (deck n) t U= gauge t U:=by funext u; rfl
def moon (P:Face (Per n)): Luster (deck n) G where
  integrand := (squareN _ P).fire
  smooth:= (squareN _ P).aqua
  solid U t:= by unfold Medal.fire; rw [square_ap,square_ap]; rw [homedeck]; simp
lemma arms : Runs (deck n):= fun i=> ⟨by simp, by simp⟩

lemma sum_energy (U : Wilson.Config G n): Wilson.energy U=∑ P:Face (Per n), (moon G n P).integrand U:=by simp only [Wilson.energy, moon, Medal.fire,square_ap]
def day : Luster (deck n) G where
  integrand := Wilson.energy
  smooth := by unfold Queue fromWax; simp_rw [sum_energy]; exact ContDiffAt.sum (fun i _=> (moon G n i).smooth)
  solid := fun u t=> by rw [homedeck]; exact Wilson.energy_gauge u t
lemma gleams : bare (day G n).caseG=(∑ P:Face (Per n), bare (moon G n P).caseG : Heave G (Edge (Site n)) (Site n) ℝ):=by unfold bare; refine (pathof G (Edge (Site n)) (Site n)).flash _ _ _ ?_; filter_upwards with x; rw [Finset.sum_apply]; exact sum_energy ..
lemma front : (day G n).caseG.val 0=0 ∧ fderiv ℝ (day G n).caseG.val 0=0 ∧ ∀ x y:ink G (Edge (Site n)), iteratedFDeriv ℝ 2 (day G n).caseG.val 0 ![x,y]=∑ P:Face (Per n),⟪(squareN _ P).arson x,(squareN _ P).arson y⟫_ℝ:=by
  refine Work.F03.hessian_of_limit ((day G n).caseG.2.of_le le_top) ?_ ?_ ?_
  · intro x; change Tendsto (fun t:ℝ=> Wilson.energy _ / _) _ _; simp_rw [sum_energy,Finset.sum_div]; exact tendsto_finsetSum _ fun i _=> (squareN _ i).germ _
  · intro x y z; simp_rw [map_add, inner_add_left,Finset.sum_add_distrib]
  intro x y; exact Finset.sum_congr rfl fun _ _=> real_inner_comm ..
end YM.MSBar.Odom
