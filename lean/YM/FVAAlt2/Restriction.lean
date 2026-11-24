import YM.FVAAlt2.SlicePull

/-! Formula for the restriction of the full MS lattice action to Landau.

Classical nonlinear ghost vertex is recovered exactly, not just the quadratic part.
`fpLetter=A ↦ (−detMatrix A i j)`: 
`fpLetter` is real with a true identity germ by construction (roam step rule).
On the ball the negative `paneGhost` normalized by its `paneLap` kinetic
has exactly these matrix coefficients, determinant `LANDweight/Jacob` for
its negative there. Signs here are antighost first then ghost.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open Lattice Finset Pert.Orb SchemeRG11.Sway Function
open MS MS.Koszul MS.Native MS.Plane MS.Landau MS.Cylinder MS.Cylinder.Taylor MS.Book
open MS.Bare MS.Bare.Focus MS.Cylinder.Lab MS.Native.Chart MS.Native.Wilsonian
open Filter Topology
open scoped ContDiff
set_option linter.unusedSectionVars false

variable {G:Gauge}{n:Side}
local notation "X" => Land G n
local notation "U" => ScalarGhost G n
variable {ι κ:Type} [Fintype ι][DecidableEq ι][Fintype κ][DecidableEq κ]
variable (A:Module.Basis ι ℝ (Land G n))(b:Module.Basis κ ℝ (ScalarGhost G n))

local notation "T" => Site n
local notation "L" => embeddingM A b
local notation "p4" => Draft.DotFlip
local notation "P" => Paper G (Site n)
local notation "K" => panel G (Site n)
local notation "D₀" => glow G (Site n)
local notation "𝒥" => ink (dirA4 (κ:=κ) A)
local infix:70 " ⋄ " => product isOdd

def logA (k:Mind G (Site n))(i:Eyes G (Site n)): X→ℝ := (projector k ∘ loco (drive n) i) ∘ spread G n
lemma logA_germ (k:Mind G (Site n))(i:Eyes G (Site n)): germ (logA k i):=by
  apply ContDiffAt.comp (g:=projector k ∘ loco (drive n) i)
  rw [map_zero]; exact (projector k).contDiff.contDiffAt.comp (f:=loco (drive n) i) 0 (ride _ i)
  exact (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Land G n) (F:=Chart.City G T) (spread G n)).contDiffAt

def response (k:Mind G (Site n))(v:ScalarGhost G n) : X→ℝ := ∑ i:Eyes G (Site n), (projector i v.val) • logA k i
lemma response_germ (k:Mind G T)(v:U): germ (response k v):=by unfold response; rw [show (∑ i:Eyes G (Site n),(projector i v.val) • logA k i) = fun x=> ∑ i:Eyes G (Site n),(projector i v.val) • logA k i x from funext fun x=> by rw [Finset.sum_apply]; rfl]; exact ContDiffAt.sum (fun i _=> (logA_germ k i).const_smul (projector i v.val))
lemma response_eq (k:Mind G T)(v:U)(x:X): response k v x=projector k (roam (drive n) (spread G n x) v.val):= by
  unfold response; conv_rhs=> rw [← Native.frame v.val]
  simp_rw [map_sum,map_smul,Finset.sum_apply]; rfl

lemma fp_expansion (u v:ScalarGhost G n): fpWeight u v = ∑ k:Mind G (Site n), ((1/2:ℝ) * projector k (gM u).val) • response k v:=by
  funext x; rw [Finset.sum_apply,Fintype.sum_prod_type]; simp_rw [Pi.smul_apply,response_eq,projector_k]; unfold fpWeight
  simp_rw [Work.F03.inner_color, Finset.sum_div]; refine Finset.sum_congr rfl fun x _=>?_ ; refine Finset.sum_congr rfl fun a _=>?_ ; ring
lemma fp_germ4(u v:ScalarGhost G n):germ (fpWeight u v):=by rw [fp_expansion]; rw [show (∑ i:Mind G (Site n), ((1/2:ℝ)*projector i (gM u).val) • response i v) = fun x=> ∑ i:Mind G (Site n), ((1/2:ℝ)*projector i (gM u).val) • response i v x from funext fun x=> by rw [Finset.sum_apply]; rfl]; exact ContDiffAt.sum (fun k _=> (response_germ k v).const_smul ((1/2:ℝ) * projector k (gM u).val))

lemma pull_stone4 (k:Mind G T):
    pull L (Focus.stone (D₀) (Chart.loco (drive n)) k)=
      ∑ j:κ, atLetter (gh j) ⋄ 𝒥 (response k (b j)):=by
  let f(i:Eyes G T):= projector k ∘ loco (drive n) i
  have hg(i:Eyes G T): germ (f i):= (projector k).contDiff.contDiffAt.comp (f:=loco (drive n) i) 0 (ride _ i)
  unfold response Focus.stone; rw [map_sum]
  simp_rw [pull_product (embTie A b), show ∀ i:Eyes G T,pull L (ink (D₀).e0 ((D₀).seed k ∘ loco (drive n) i))= 𝒥 (logA k i) from fun i=> embedding_ink A b (hg i), pull_ghostPi A b,
    map_sum,LinearMap.sum_apply]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _=>?_
  rw [ink_sum (F:=fun i=> (projector i (b j).val) • logA k i) _ _ (fun i _=> (logA_germ k i).const_smul (projector i (b j).val)),map_sum]
  refine sum_congr rfl fun s _=>?_; rw [ink_smul _ (logA_germ k s),projector_k,map_smul,map_smul,LinearMap.smul_apply] 

local notation "𝒮" => launch (glow G T) (colorTerm G T) (loco (drive n))
def fpLetter (b:Module.Basis κ ℝ (ScalarGhost G n))(i j:κ)(x:Land G n):ℝ:= fpWeight (barBasis b i) (b j) x

lemma ghost_matrix (i j:κ):fpLetter b i j =ᶠ[𝓝 0] fun x=> -(b.coord i ((paneLap G n).symm (paneGhost G n x (b j)))):= by
  filter_upwards [fp_germ (barBasis b i) (b j)] with x hx; exact hx.trans (congrArg Neg.neg (ghost_dual b _ _))
lemma fp_flat (i j:κ): fpLetter b i j 0= -(if i=j then 1 else 0):= by
  unfold fpLetter; rw [(show fpWeight (barBasis b i) (b j) 0 = -siteTest (barBasis b i) (paneGhost G n 0 (b j)) from mem_of_mem_nhds (s:={x:Land G n|fpWeight (barBasis b i) (b j) x= -siteTest (barBasis b i) (paneGhost G n x (b j))}) (fp_germ (barBasis b i) (b j))), ghost_start b i j] -- maybe .eq_of_nhds needs shape

def ghostAction : Raw (Alpha ι κ) ℂ:= ∑ i:κ,∑ j:κ, atLetter (antigh i) ⋄ (atLetter (gh j) ⋄ 𝒥 (fpLetter b i j))
lemma pull_hung : pull L ((1/2:ℂ) • (P).hung 𝒮)= ghostAction A b:= by
  rw [Bonded.hung,(K).split_i,map_smul,map_add,map_sum,map_sum]; simp_rw [feeA,one_smul,launch_stone,pull_product (embTie A b),pull_KPi A b,pull_stone4,map_smul,pull_product (embTie A b),pull_BPi A b,map_zero, LinearMap.zero_apply,smul_zero,Finset.sum_const_zero,add_zero]; -- sums
  simp_rw [map_sum,LinearMap.sum_apply, Finset.smul_sum]; unfold ghostAction fpLetter; simp_rw [fp_expansion]
  let f(k:Mind G T)(j i:κ):= ( (1/2:ℂ) * ↑((gM (barBasis b i)).val k.1 k.2) ) • (atLetter (antigh i) ⋄ (atLetter (gh j) ⋄ 𝒥 (response k (b j))))
  calc
    _ = ∑ k:Mind G T, ∑ j:κ, ∑ i:κ,f k j i:=by
      simp_rw [map_smul,LinearMap.smul_apply,smul_smul]; rfl
    _ = ∑ i:κ,∑ j:κ,∑ k:Mind G T, f k j i:= by
      conv_lhs=> arg 2; intro k; rw [Finset.sum_comm]
      rw [Finset.sum_comm]; exact sum_congr rfl fun i _=> Finset.sum_comm
    _ = _:= by
      refine sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_ ; let v:= barBasis b i; let Q:=fun k:Mind G T=> ((1/2:ℝ)*projector k (gM v).val)
      change _= product _ _ ((product _ _) (𝒥 (∑ k:Mind G T, Q k • response k (b j))))
      rw [ink_sum (F:=fun k=> Q k • response k (b j)) _ _ (fun k _=> (response_germ k (b j)).const_smul (Q k)),map_sum,map_sum]; apply sum_congr rfl; intro k hk
      rw [ink_smul _ (response_germ k (b j)), map_smul,map_smul]; unfold Q; rw [projector_k]; unfold f; push_cast; rfl


lemma LANDsmooth : germ (LAND (G:=G) (n:=n)):=by rw [LAND_eq]; exact VL_smooth
lemma on_W : pull L ((1/2:ℂ) • docket n (Wilsonian.W G))=
    - 𝒥 LAND + ghostAction A b := by
  rw [witnessD,Sourced,smul_add,map_add,pull_hung, map_smul, show (glow G (Site n)).e0=direction from rfl,embedding_ink A b (rent_s (G:=G) (drive n)), show Chart.rent (drive n) ∘ (⇑(spread G n))=(-2:ℝ) • LAND (G:=G) (n:=n) from funext fun x:X => rent_land x, ink_smul _ (LANDsmooth (G:=G) (n:=n))]
  push_cast; rw [smul_smul]; norm_num

lemma on_H (hn : Admissible n): pull L ((1/2:ℂ) • docket n (Wilsonian.H G))=
    𝒥 (fun x=>Real.log (Jacob x.val)):=by
  have hx: germ (fun x:X=> Real.log (Jacob x.val)):= by
    apply ContDiffAt.comp (g:=Real.log ∘ Jacob) (f:=g0 G n)
    rw [map_zero]; exact ContDiffAt.log (Pert.Orb.jacobian_smooth) (by simp)
    exact (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Land G n) (F:=Potential G n) (g0 G n)).contDiffAt
  rw [shiftD,map_smul,show (glow G (Site n)).e0=direction from rfl,
    embedding_ink A b (Chart.nice_totalH)]
  have he: totalH ∘ (⇑(spread G n))=ᶠ[𝓝 0] (2:ℝ) • (fun x:Land G n=> Real.log (Jacob x.val)):=by
    filter_upwards [jac_log (G:=G) hn] with x hv
    change totalH (spread G n x) = 2 * Real.log _; rw [hv]; ring
  rw [inkit _ he, ink_smul _ hx, smul_smul]; norm_num

end YM.FVAAlt2
