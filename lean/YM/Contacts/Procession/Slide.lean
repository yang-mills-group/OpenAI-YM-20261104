import YM.Contacts.Procession.Recode
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Procession.Catch
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Welcome Resetter
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
variable {α β ι:Type}[Fintype ι]{G:Gauge}{σ:ℝ≥0}{T:TableFee}{p m d k t i r:ℕ}
-- base boost p+2
abbrev cap (p:ℕ):=p+2
variable (w:Resetter.Pow) {F:House α}
def swell (p:ℕ)(F:House α):=lowerHouseMark w (Catch.cap p) (shiftA (Catch.cap p) F)
def recoil (p:ℕ)(F:House α)(i:ℕ):= Catch.swell w p F (i+Catch.cap p)
lemma restrictTurn (j:ℕ)(u:ℕ)(hw:∀ i≤j,F i r=0)(h:Resetter.Uniform w): lowerHouseMark w t F j r=0:= by
   induction j using Nat.strongRecOn with| _ i ih =>
      by_cases he:r ≤ i+2
      · rw [translatedMark w t F he h,hw i le_rfl,sum_eq_zero,sub_self]; intro j hj; unfold dazzle; split; swap; simp
        rw [ih (j+r-2) (by rw [Finset.mem_range] at hj; omega) (fun t ht=>hw t (by rw [Finset.mem_range] at hj; omega)),smul_zero]
      unfold lowerHouseMark flipBack; rw [if_neg he]
lemma reclip (h:Resetter.Uniform w) : (shiftA (Catch.cap p) (recoil w p F))= Catch.swell w p F:= by
   ext1 i; unfold shiftA; split
   next hi=>exact congr_arg (Catch.swell w p F) (Nat.sub_add_cancel hi)
   next hi=> ext1 r; exact (restrictTurn w _ 0 (h:=h) (fun i' he=> show shiftA (Catch.cap p) F i' r=0 from (by unfold shiftA; rw [if_neg (by omega)]; rfl))).symm -- if_neg under apply
lemma terror (hp:Proper p F)(h:Resetter.Uniform w): Proper p (recoil w p F):= by
   let Y:= shiftA (Catch.cap p) F; have he:Snug Y:= tagged hp (by unfold Catch.cap; omega) (by unfold Catch.cap; omega); refine ⟨fun i k=>?_,fun i r hi=> restrictTurn w _ 0 ?_ h⟩ -- syntax he
   · exact (presage_formMark w _ Y (⟨fun _ _=> he.poems _ _, fun _ _ h=>he.thin _ _ (by omega)⟩: Shaped Y) h).poem _ _
   intro j hj; unfold shiftA; split; apply hp.thin; unfold Catch.cap at *; omega; rfl -- catches
variable {n:Side}
theorem stamp {F:House (Lines G n 1)} (h:Resetter.Uniform w)(hw:Nation G n p F): Nation G n p (recoil w p F):=⟨terror w hw.proper h,fun k=>by rw [show shiftA (p+2) _ = _ from reclip w (F:=F) (p:=p) h]; exact sealsMark w _ h (hw.birth k)⟩
-- marker projection compatibility. Exact reexpression in own native normalized fields: point
-- coefficient of boost-old g^(cap p + 2) compared through same boost-new (permits
-- integer charged curvature log). 'rockW w t' precisely `rotate^(-t-2)`,
-- via rotated_power. Does not substitute the small-coupling trajectory here.
theorem carried (h:Resetter.Uniform w) (t:ℕ)(F:House α) (i r:ℕ): dazzle (shiftA (Catch.cap t) F) i r= ∑ j∈Finset.range (i+1), pin (rockW w (Catch.cap t) * (PowerSeries.X*Resetter.rotate w)^j) i • dazzle (shiftA (Catch.cap t) (recoil w t F)) j r:= by simp_rw [reclip w h]; exact rehouseMark w _ _ h i r -- edit
-- moment price and transfer compatibility on the same width
variable {X:House (Node α)}{y:α} {B: TableFee}
def meter (w:Resetter.Pow)(t:ℕ)(V:TableFee)(i n:ℕ):ℝ:= V n i + ∑ j∈Finset.range n, ‖tickerMark w t j n‖ * (if _h:j<n then meter w t V i j else 0)
termination_by n
def mU (w:Resetter.Pow)(t:ℕ)(V:TableFee)(i j:ℕ) := if j ≤ i+2 then meter w t (ledBase V) j (i+2-j) else 0
def U (V: TableFee)(t i j:ℕ):ℝ:= if t≤ i then V (i-t) j else 0
private lemma invest (h:Price X y σ B)(i r:ℕ)(t:ℕ): Rest (terrain σ α) (0,y) (dazzle X i r) (ledBase B i r) := by unfold dazzle ledBase; split; apply h.lands; apply Rest.zero
private lemma go (h:Price X y σ B)(i k:ℕ) : Rest (terrain σ α) (0,y) (presageMark w t (dazzle X) k i) (meter w t (ledBase B) i k):= by
    induction k using Nat.strongRecOn with| _ k ih=>
    rw [presage_eqMark,meter]; refine Rest.sub (invest h _ _ 0) (Rest.sum (fun j hj=> ?_)); rw [dif_pos (Finset.mem_range.mp hj)]; exact (ih j (Finset.mem_range.mp hj)).smul _ -- funds not val
lemma xin (p n:ℕ)(h:Price X y σ B): Price (shiftA p X) y σ (U B p):= by refine ⟨fun i j=>?_⟩; unfold shiftA U; split; exact h.lands ..; apply Rest.zero
lemma finance (p':ℕ)(h:Price X y σ B): Price (lowerHouseMark w p' X) y σ (mU w p' B):=by refine ⟨fun i j=>?_⟩; unfold mU lowerHouseMark flipBack; split; exact go w h ..; apply Rest.zero
def stool (p:ℕ)(B:TableFee)(i j:ℕ):ℝ:= mU w (Catch.cap p) (U B (Catch.cap p)) (i+Catch.cap p) j
lemma moving (p:ℕ)(h:Price X y σ B): Price (recoil w p X) y σ (stool w p B):=⟨fun i j=> (finance w _ (xin (Catch.cap p) 0 h)).lands ..⟩
lemma sub_cols (F K : Pulse.Field (Fin p) (Node α))(k:Node α→β)(hf: Summable F)(hk:Summable K) : packing k (F-K)=packing k F-packing k K:= funext fun y=> by simp only [packing,cram,Pi.sub_apply]; exact (hf.subtype _).tsum_sub (hk.subtype _)
lemma smul_pack (F:Pulse.Field (Fin p) (Node α))(k:Node α→β)(a:ℝ): packing k (a • F)= a • packing k F:= by ext1 x; simp only [packing,cram,Pi.smul_apply,smul_eq_mul,tsum_mul_left]
lemma preserveFoot (h:Price X y σ B) (k:Node α→β) : plead (Catch.swell w t X) k=lowerHouseMark w (Catch.cap t) (plead (shiftA (Catch.cap t) X) k) := by
   funext i r; let J:=shiftA (Catch.cap t) X; let W:=plead J k; let Y:=presageMark (α:=Node α) w (Catch.cap t); have hJ := xin (Catch.cap t) 0 h; unfold plead Catch.swell lowerHouseMark flipBack; split; rotate_left; · ext1 p; simp [packing,cram]
   suffices hz:∀ i, packing k (Y (dazzle J) i r)= presageMark w (Catch.cap t) (dazzle W) i r by exact hz _
   intro i; induction i using Nat.strongRecOn with| _ i ih =>
   unfold Y; have ht b : packing k (dazzle J b r)= dazzle W b r:= by unfold dazzle; split; rfl; ext1 x; simp [packing,cram]
   let F(x):= tickerMark w (Catch.cap t) x i; have hS x: Summable (F x • presageMark w (Catch.cap t) (dazzle J) x r):=((go w (t:=Catch.cap t) hJ r x).smul (F x)).summ
   rw [presage_eqMark,presage_eqMark w (Catch.cap t) (dazzle W),sub_cols,pack_sum,ht]; apply congr_arg; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [smul_pack,ih i (Finset.mem_range.mp hi)]
   · intro t _; exact hS t
   · exact (invest hJ i r 0).summ
   rw [show _ = _ from (show (∑ t∈Finset.range i,F t • Y (dazzle J) t r)=(fun x=>∑ t∈Finset.range i,(F t • Y (dazzle J) t r) x) from funext fun x=> Finset.sum_apply ..)]; exact summable_sum fun i _=>hS i
lemma pledgeShift (H:House α)(k:α→β): plead (shiftA t H) k=shiftA t (plead H k):=by unfold plead; funext i r; unfold shiftA; split; rfl; ext1 p; simp [packing,cram]
theorem recoiled (h:Price X y σ B)(k:Node α→β) : plead (recoil w t X) k=recoil w t (plead X k):= by
    funext i j; let Z:= shiftA (X:=β) (Catch.cap t); let Y:= plead X k; change plead (Catch.swell w t X) k _ j= lowerHouseMark w (Catch.cap t) (Z Y) _ j; rw [preserveFoot w h k, pledgeShift]; -- defeq
lemma caring {X:bore G}{y:Dye G}(h:Mount (G:=G) X p)(hp:Price X y σ B)(hh:Resetter.Uniform w): Mount (G:=G) (recoil w p X) p:= ⟨terror w h.incarnate hh, fun i=>by rw [recoiled w hp]; exact Catch.stamp w hh (h.attends i)⟩ -- X α vs Dye
end YM.Contacts.Procession.Catch
