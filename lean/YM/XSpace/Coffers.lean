import YM.XSpace.Cargo
/-!
# The raw frontages for triangle (compare grade six)

Here grouping RHS into convenient representations to bill. Need choose mesh behind
any given shape, not a collection of angular-dependent RG schemes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Graph3
open Function Set Filter Lattice Trace Chart2 Maxwell Maxwell.Free Foundation Shade JetGauge Outline MvPolynomial Structure1 Chiral Finsupp Mu Normalize Next.Rank.Normal Stall Pages Furlough Contraction
open scoped Topology BigOperators InnerProductSpace Classical
variable {G:Gauge} {n:ℕ} (W:Initialize G)(g:G.Simple) (c:Shade.Cut)(a:ℝ)(z x y:Cover)
local notation "A" => b_w W z
local notation "L" => u_w W x
local notation "M" => u_w W y
local notation "K" => base a
variable {ω : Type*} (d: ℕ)
abbrev trip (z x y:ω): Fin 3→ω := ![z,x,y]
lemma peg₀ (x y z:ω): trip x y z 0=x:=rfl
lemma peg₁ (x y z:ω): trip x y z 1=y:=rfl
lemma peg₂ (x y z:ω): trip x y z 2=z:=rfl
def token (G:Gauge): Tags G 6 3:= trip (en (le_refl 6) (Bfield G)) (en (show 4≤6 by decide) (Ufield G)) (en (show 4≤6 by decide) (Ufield G))
-- no self restrictions here

def σP (p:HP G n): Stamp G:=rf W c n a p
def versus (p:HP G n): Stamp G:= stars W z p-Trace.volume z (σP W c a p)
lemma begins (P:HP G n)(x:Cover)(h:n≤d): μ0 W d a x (en h P)= base a^n • freeze (slack W x P):=by rw [μ0,entry,base_ice0,snaps,map_smul]
def μ' : Sec G d→ₗ[ℂ] Stamp G:= μ1 W d a z - μ0 W d a z ∘ₗ Structure1.ready W c a d
lemma clearsMark (ha: 0<a)(p:HP G n)(h:n≤d): μ' W c a z d (en h p)= base a^n • freeze (versus W c a z p):=by unfold μ' μ1 versus; rw [LinearMap.sub_apply,LinearMap.comp_apply,entry,base_ice1,ready_one,classFee,LinearMap.smul_apply,LinearMap.comp_apply,map_smul, map_smul,canal W z a ha,map_sub,smul_sub]; rfl

variable {d}
abbrev shifts (x:Fin n→Cover): Point G d n:= (blossom1 W d a x)- lot (blossom0 W d a x) (Structure1.ready W c a d)
lemma shaken (p:Tags G d n)(x:Fin n→Cover): shifts W c a x p= ∑ i: Fin n, E (root G) (wind d (update (fun j=> μ0 W d a (x j)) i (μ' W c a (x i) d)) p):=by simp only [shifts,_root_.sub_apply,lots,blossom1,_root_.sum_apply,LinearMap.compMultilinearMap_apply,pointed,pointer, ← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [μ',LinearMap.sub_apply,LinearMap.comp_apply,sub_mul,map_sub]
abbrev Vb (V:Face ℤ):= tie G A (V3 G V)
abbrev plum (T:Fin 3→ Stamp G):=∏ i,T i
def spell : ℂ:= F3 (versus W c a z (Bfield G)) L M+ F3 A (versus W c a x (Ufield G)) M + F3 A L (versus W c a y (Ufield G))
private lemma trio (P Q R: Stamp G)(k:ℂ): E (root G) ((k^6 • freeze P)*(k^4 • freeze Q)*(k^4 • freeze R))= k^14 * F3 P Q R :=by rw [smul_mul_smul,smul_mul_smul, ← pow_add, ← pow_add,map_smul,ζ_value,mul_assoc]; rfl
lemma pillars (ha:0<a): shifts W c a (trip z x y) (token G)=base a^14*spell W c a z x y:=by
  simp only [shaken, Fin.sum_univ_three, winds,Fin.prod_univ_three]; -- write one finite-case proof using helper rewriting
  simp only [token,Function.update_self,peg₀,peg₁,peg₂]; rw [Function.update_of_ne (show (0:Fin 3)≠1 by decide), Function.update_of_ne (show (0:Fin 3)≠2 by decide), Function.update_of_ne (show (1:Fin 3)≠0 by decide), Function.update_of_ne (show (1:Fin 3)≠2 by decide), Function.update_of_ne (show (2:Fin 3)≠0 by decide), Function.update_of_ne (show (2:Fin 3)≠1 by decide)]; simp only [peg₀,peg₁,peg₂,begins,clearsMark W c a _ _ ha]
  simp_rw [trio]; rw [spell,mul_add,mul_add]
lemma canon (P: Face ℤ): snow W 6 a (trip z x y) P (token G)=base a^14* F3 (Vb W z P) L M:=by
  simp only [snow,LinearMap.compMultilinearMap_apply,winds,token, Fin.prod_univ_three]; simp only [peg₀,peg₁,peg₂,begins,LinearMap.comp_apply,LinearMap.mulLeft_apply]; rw [smul_mul_smul,smul_mul_smul]; -- actually maybe Fin.prod order; inspect
  rw [← pow_add,← pow_add,mul_smul_comm,map_smul,ζ_value]; change _* E (root G) (V3 G P *((freeze A * freeze L) * freeze M)) = _; rw [Vb, out,show freeze (G:=G) (V3 G P)= V3 G P from no_twin (by rw [gone,opens_V])]; change K^(14:ℕ)* _=K^14*_; apply congr_arg; apply congr_arg; ring
end YM.XSpace.Graph3
