import YM.FormalOPE.RG10.Position.Grade

/-! # Algebra of logarithmic rails before extracting or assuming any running-coefficient bound -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Position.Grade
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle Matrix
open scoped Topology BigOperators ContDiff Classical
variable {J K : Type*} [Fintype J] [DecidableEq J] {w:J→ℕ}

structure Flow where
  psi : ℝ→ fps
  interior s : constantCoeff (psi s)=0
  tangent s : coeff 1 (psi s)=1
namespace Flow
variable (g:Flow) (s t:ℝ)
def warp : fps→+*fps:= PowerSeries.substAlgHom (R:=ℝ) (Triangle.good _ (g.interior s))
lemma warped (P:fps) : g.warp s P=subst (g.psi s) P:= congr_fun (coe_substAlgHom (R:=ℝ) (Triangle.good _ (g.interior s))) P
lemma kept (P:fps) : constantCoeff (g.warp s P) = constantCoeff P:= by rw [g.warped]; exact Triangle.substitutes_zero (g.interior _)
lemma at_const (x:ℝ): g.warp s (C x)=C x:= by rw [g.warped,PowerSeries.subst_C]; rfl
lemma at_power (n:ℕ) : coeff n ((g.psi s)^n)=1:= by
 let P :fps:= PowerSeries.mk fun i=>coeff (i+1) (g.psi s)
 have hp : g.psi s=X*P:= by nth_rw 1 [(g.psi s).eq_X_mul_shift_add_const]; rw [g.interior,map_zero,add_zero]
 rw [hp,mul_pow,PowerSeries.coeff_X_pow_mul',if_pos le_rfl,Nat.sub_self,coeff_zero_eq_constantCoeff_apply,map_pow]; simp [P,g.tangent]
lemma through (P:fps)(n:ℕ): coeff n (g.warp s P)=coeff n P + ∑ j∈Finset.range n, coeff j P * coeff n (g.psi s ^ j):= by
 rw [g.warped,AlignSeries.subst_finite (g.interior s), Finset.sum_range_succ_comm,at_power,mul_one]
end Flow

namespace Units -- inspect
end Units
variable (w) in
def stone (s:ℝ):Matrix J J ℝ:= Matrix.diagonal (fun i=>Real.exp (-s*w i))
variable (M L : Matrix J J fps)
local notation "K" => Matrix J J fps

def stamp (n:ℕ) : Matrix J J ℝ:= M.map (coeff n)
omit [Fintype J] [DecidableEq J] in
@[simp] lemma stamp_apply (i :ℕ)(j k:J): stamp M i j k=coeff i (M j k):=rfl
omit [Fintype J] [DecidableEq J] in
lemma canvas : stamp M 0=M.map constantCoeff:=Matrix.ext fun _ _=>coeff_zero_eq_constantCoeff_apply _
omit [Fintype J] [DecidableEq J] in
lemma canvas_tile (n) : stamp (tile w M) n=tile w (stamp M n):=by ext i j; by_cases h:w i=w j<;> simp [tile,h]
structure Passe (g:Flow) (w:J→ℕ) where
  train (s:ℝ) : Matrix J J fps
  full s : stamp (train s) 0=stone w s
  rank s : Cut w (train s)
  law (s t:ℝ) : ((train s).map (g.warp t)) * train t = train (s+t) -- psi_t subst. commutativity RHS
  home : train 0=1

-- weighted closed costs are declared branch, not derived until post polynomial work.
namespace Passe
variable {g:Flow} (h:Passe g w) (s t:ℝ)
-- grade block propagates as true group--see law orientation
omit [Fintype J] in
lemma stone_layer : Layer w (stone w s) := fun i j (he:w i≠w j)=> Matrix.diagonal_apply_ne _ (fun h=>he (h ▸ rfl)) -- order?

def drive := tile w (h.train s)
lemma stationed : stamp (h.drive s) 0=stone w s:=by rw [drive,canvas_tile,h.full]; exact layer_fixed (stone_layer _)
lemma station_block : Layer w (h.drive s):=tile_layer
lemma station_law : ((h.drive s).map (g.warp t))*h.drive t=h.drive (s+t):=by
 rw [drive,← tile_map,drive,drive, ← Cut.tile ((h.rank s).carries (g.warp t)) (h.rank t), h.law]
lemma station_base : h.drive 0=1:= by rw [drive,h.home]; exact layer_fixed (tiled_one w)
end Passe
end YM.FormalOPE.RG10.Position.Grade
