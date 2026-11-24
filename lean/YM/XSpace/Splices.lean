import YM.Next.RANK.GlowLine
import YM.Next.RANK.Scars
import YM.XSpace.WickLabels

/-!
# Reconcile jet reads with mixed difference stencils on any cross lines

Exploit the available `Next.Rank` library for exact interpolation on *closed*
discrete curvature cochains. Its remains bound proves a nice algebraic consequence:
apply ANY bright linear form pure/vanishing below level j; modulo the subspace of
Bianchi equations it is a finite linear combination of *plain plaquette differences*,
all of order EXACTLY j. No requirement every raw Taylor moment vanishes on unrestricted
tensors (probably untrue for these stencils). This solves both-end cancellations
simultaneously. Work with real colors for now.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Cross
open Lattice Filter Set Function Labels Source Source.Drops
open Next.Rank Configuration Beamer
open scoped Topology BigOperators
variable {G : Gauge} {j r : ℕ}

lemma included {x : Cover} (h : street x≤r): x∈ Lattice.box r:=by
  apply Lattice.box_test.mpr; have ht (i : Axis) : (x i).natAbs ≤ r := (Finset.single_le_sum (f:=fun i=> (x i).natAbs) (fun _ _=> Nat.zero_le _) (Finset.mem_univ i)).trans h; constructor <;> intro i <;> specialize ht i <;> omega

-- finite lifted difference reads on a fixed stencil type
abbrev Reading (G : Gauge) (j r : ℕ) := (↥(Lattice.box r)) × PlaqAxes × G.ColorIndex × (Fin j → Axis)
def mood (i : Reading G j r) : Degree G:= ⟨i.2.1,i.2.2.1,i.1,j,i.2.2.2⟩
lemma corner (L : Degree G) (h : L.degree=j) (hp : L.point∈Lattice.box r): ∃ i : Reading G j r,L=mood i:=by
  rcases L with ⟨a,b,c,j',d⟩; change j'=j at h; subst j; exact ⟨(⟨c,hp⟩,a,b,d),rfl⟩

def Starts (j : ℕ) (L : Module.Dual ℝ (Horizon G)) := ∀ i < j, ∀ A : Labels.Taylor G i, L (sweep i A)=0
lemma kills_lower (L : Module.Dual ℝ (Horizon G)) (h : Starts j L) (f : Horizon G) : L (cloud (j+1) f)=0 := by
  rw [cloud,map_sum]; apply Finset.sum_eq_zero; intro i _; rw [map_smul, tester,h i.val.1 (by have he:= i.property; unfold Labels.generation at he; omega),smul_zero]

lemma removes (L : Module.Dual ℝ (Horizon G)) (hl : bright L) (hp : Starts j L) :
    ∃ (r : ℕ) (c : Reading G j r→ℝ), ∀ f:Horizon G, shutter f → L f=∑ p,c p*gesture (mood p) f:=by
  classical
  obtain ⟨w,hw⟩:=hl
  let r:= w.support.sup fun i=> street i.1
  let B (L : Module.Dual ℝ (Horizon G)): Module.Dual ℝ (signal G) := L ∘ₗ (signal G).subtype
  let v (i : Reading G j r) := B (gesture (mood i))
  have he:B L∈Submodule.span ℝ (range v):=by
    apply mem_span_of_iInf_ker_le_ker; intro x hx
    have ht (i : Degree G) (h : i.degree=j) (p : street i.point≤r) : gesture i x.val=0:=by obtain ⟨z,rfl⟩:= corner i h (included p); exact (Submodule.mem_iInf _).mp hx z
    have H (i : Address G) (h : i∈ w.support) : x.val i=cloud (j+1) x.val i:=by
      have hh (L : Degree G) (hg : L.degree=j+1-1) (p : street L.point ≤ r) : ‖gesture L x.val‖≤0:= by rw [ht L (by omega) p,norm_zero]
      have hv:= remains x.val x.property 0 le_rfl r hh i (Finset.le_sup (f:=fun i : Address G=>street i.1) h); rw [mul_zero] at hv; exact sub_eq_zero.mp (norm_le_zero_iff.mp hv)
    change L x.val=0; rw [← kills_lower L hp x.val,hw,hw]; exact Finset.sum_congr rfl (fun i h=> congr_arg (w i • ·) (H i h))
  obtain ⟨c,hc⟩:=(Submodule.mem_span_range_iff_exists_fun ℝ).1 he
  refine ⟨r,c,fun f h=>?_⟩; have he:=LinearMap.congr_fun hc ⟨f,h⟩; rw [LinearMap.sum_apply] at he; exact he.symm

-- Reads on this `Survey` satisfy that hypothesis through any key dealt with.
variable {d : ℕ} {H : Hol G} (A : Survey G H d)

def service (i : Top.Bean A): Module.Dual ℝ (Horizon G):=LinearMap.proj ((A.looks i.1).offset,(A.looks i.1).plaq,i.2)
lemma at_bean (i : Top.Bean A) (f) : service A i f=f ((A.looks i.1).offset,(A.looks i.1).plaq,i.2):=rfl

def passenger (f : Horizon G) : GaugePanel G A.size:= fun i=>WithLp.toLp 2 fun j=>service A ⟨i,j⟩ f

def looks (L : Module.Dual ℝ (Snap G d)) : Module.Dual ℝ (Horizon G):=∑ i:Top.Bean A,Top.bills A L i • service A i
lemma uses (L : Module.Dual ℝ (Snap G d)) (f : Horizon G) : looks A L f=L (A.extract (passenger A f)):=by
  rw [looks,LinearMap.sum_apply]; conv_rhs=> rw [← Top.bean_reconstruct A (passenger A f),map_sum,map_sum]
  refine Finset.sum_congr rfl fun i _=>?_; rw [LinearMap.smul_apply,map_smul,map_smul]; exact mul_comm (Top.bills A L i) (service A i f)
lemma blossoms (L : Module.Dual ℝ (Snap G d)): bright (looks A L) := bright_sum _ _ fun i _=> bright_scale ⟨Finsupp.single ((A.looks i.1).offset,(A.looks i.1).plaq,i.2) 1,fun f=> by rw [at_bean,Finsupp.linearCombination_single,one_smul]⟩ _

def tick {j : ℕ} (h : j+2≤d) (x : Labels.Taylor G j): Snap G d := Pi.single ⟨j,by omega⟩ x
lemma ticks {j : ℕ} (h : j+2≤d) (x : Labels.Taylor G j): expand d (tick h x)=Pi.single j x:=by
  classical
  funext i; by_cases H:i=j
  · subst i; simp only [expand,dif_pos (show j<d-1 by omega),tick, Pi.single_eq_same]
  rw [Pi.single_eq_of_ne H]; unfold expand tick; split; rename_i he; rw [Pi.single_eq_of_ne (show (⟨i,he⟩:Fin (d-1)) ≠ ⟨j,by omega⟩ from Fin.ne_of_val_ne H)]; rfl

lemma swept (h : j+2≤d) (x : Labels.Taylor G j) : passenger A (sweep j x)= A.glowing (tick h x) :=by
  let f : Horizon G:= fun i=> Spindle.oneGlow d (tick h x) (i.1,i.2.1) i.2.2
  have ht : f=sweep j x:= by
    funext q
    let a:=q.2.1; rcases q with ⟨q,v,s⟩
    unfold f; dsimp only; rw [Spindle.glows, ticks h x,Finset.sum_eq_single j]
    · rw [Pi.single_eq_same]; rfl
    · intro i _ hi; rw [Pi.single_eq_of_ne hi]; ext l; exact congr_fun (map_zero (sweep i (G:=G))) (q,v,l)
    intro hh; rw [Finset.mem_range] at hh; omega
  rw [← ht]; rfl
lemma extracts (h : j+2≤d) (x : Labels.Taylor G j) : A.extract (passenger A (sweep j x))=tick h x:= by rw [swept A h x,A.linear_jet]

lemma usable (k : Key G) (h : generation k ≤ d) : Starts k.1 (looks A (Survey.component k)) := by
  intro i hi x; rw [uses,extracts A (j:=i) (by unfold generation at h; omega), Survey.component_point,ticks,Pi.single_eq_of_ne (Nat.ne_of_gt hi),map_zero,Finsupp.zero_apply]
lemma end_cost (k : Key G) (h : generation k ≤ d) (x : Labels.Taylor G k.1) : looks A (Survey.component k) (sweep k.1 x)=(axes G k.1).coord k.2 x:= by rw [uses,extracts A h,Survey.component_point,ticks,Pi.single_eq_same]; rfl
end YM.XSpace.Cross
