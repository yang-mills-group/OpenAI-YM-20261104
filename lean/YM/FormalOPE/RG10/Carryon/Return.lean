import YM.FormalOPE.RG10.Carryon.Release
/-!
# Infer local applicability of leading-regime position system in reverse. If *auxiliary* frame
 beginning point near free with actual chosen labels, a close-to-identity leading lift can be
 undone, even if other orders not under analytic control (indeed often singular in cutoff). -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Carryon
open Gazebo Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle
open scoped Topology BigOperators ContDiff Classical
open PowerSeries Peal
variable {G : Gauge} {F : Frames G}{D:Stock F} {d : ℕ}
local notation "A" => PertExtension.Physical.Profile.n
local notation "V" => Mark (Deck F d) PertExtension.Physical.Profile.n
local notation "K" => Matrix (Deck F d) (Deck F d) ℝ
local notation "ins"=> PertExtension.Position.insert (Deck F d) PertExtension.Physical.Profile.n
variable {I:Type*}{l: Filter I} {X : I → Matrix (Deck F d) (Deck F d) fps}{z:I→Mark (Deck F d) PertExtension.Physical.Profile.n→fps}

abbrev prior (v:V):= raw F d v
-- naming rows
lemma forward (ht:Tendsto (fun i=> Stg (X i) 0) l (𝓝 (1:K))) (hv:listens (D:=D) (l:=l) fun i=> ins (z i) (X i)) : listens (D:=D) (l:=l) z := by
 let a i:= Stg (X i) 0; let v i:= ins (z i) (X i); let V' i (j:Mark (Deck F d) A):= constantCoeff (v i j)
 let k i := (a i)⁻¹
 have hc (i:I) : V' i = ins (fun j=> constantCoeff (z i j)) (a i):= funext fun j=> by
    unfold V' v; rw [insert_constant]; simp [a,Stg]; rfl -- instances
 have hk : Tendsto k l (𝓝 (1:K)):= ((continuousAt_matrix_inv (1:K) ((show (1:K).det=1 from Matrix.det_one) ▸ NormedRing.inverse_continuousAt (1:ℝˣ))).tendsto.comp ht).mono_right (le_of_eq (by rw [inv_one])) -- spelling
 let t:=(D d).tests; let L:= markIn (J:=Deck F d) (arity:= A) t
 have hx : ∀ᶠ i in l, IsUnit (a i).det:= (continuous_id.matrix_det.continuousAt.tendsto.comp ht).eventually (Units.isOpen.mem_nhds (by simp : IsUnit ((1:K).det)))
 have hr : ∀ᶠ i in l, probe D (z i) = ins (V' i) (k i) ∘ L := by
   filter_upwards [hx] with i hi
   rw [hc,show ins (ins _ (a i)) (k i)=ins (fun j=>constantCoeff (z i j)) (k i * a i) from insert_twice .., nonsing_inv_mul (a i) hi,diag_one]; exact funext (fun _=> (insert_one ..).symm)
 apply tendsto_pi_nhds.mpr; intro y
 have hL (j k':Deck F d): Tendsto (fun i=> k i j k') l (𝓝 ((1:K) j k')):= tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hk j) k'
 let x:= L y
 let f := (prior (F:=F) (d:=d))
 have hh: Tendsto (fun i=> ins (V' i) (k i) (L y)) l (𝓝 (ins f (1:K) x)):= tendsto_finsetSum _ fun h _ => (tendsto_pi_nhds.mp hv (show Questionnaire t from ⟨y.1,h⟩)).mul (tendsto_finsetProd _ (fun _ _=> hL _ _)) -- reduce
 rw [diag_one,show ins f (Physical.diag _) x= _ from insert_one f x] at hh; exact hh.congr' (hr.mono (fun i hi=>(congr_fun hi y).symm))
end YM.FormalOPE.RG10.Carryon
