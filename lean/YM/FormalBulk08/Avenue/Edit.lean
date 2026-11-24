import YM.FormalBulk08.Avenue.Stamp
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Avenue
open Filter Set Metric MeasureTheory Function Lattice Laurent Bloch Exterior Precision RG Next.Free
open Stationary
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
variable {n:Side}
open MSbar.Tree.Resolvent
variable {j:ℕ}{k:ℝ}
open Flat UVExtension.Free
variable {G:Gauge}
open Reef Mesa Gorge

variable {D l:ℕ}
open Kemp Pose Dawn Spigot Orb Wick Series Jets MeasureTheory Lotus Shore Lava Rift
open Grail
variable {x:Loc G 1}{η σ A B C:ℝ}{u r p:ℕ} {q:edgeL G→edgeL G→ℝ}
-- exact Kalm & cream for any test mark at leading
open City PowerSeries
open Roof Wine Source Source.Drops Labels
variable {o:Loc G 1} {d:ℕ}
-- n chief ix depends support tier
def clover (F:Frame G d)(v:Train j)(k:ℝ)(Y: Anthem D G)(l:ℕ) (i:Letter F):= pearlJ F (winner v k l Y (Pose.inside F i D) (slots F i)) (mint F i)
def preTable {V:Type*} (T:Matrix V V Pence) : Matrix V V ℝ:=Matrix.of fun i j=>coeff 0 (T i j)
def noncontract (F:Frame G d)(T:Matrix (Letter F) (Letter F) Pence): Matrix (Letter F) (Letter F) ℝ:= fun i j=> if slots F i=slots F j then coeff 0 (T i j) else 0
lemma mood_nil (a:hue G)(P:Flight j u)(V:Lodge P.patch)(K:KernelChoices)(W:Pot G)(ρ:ChartRatio G)(h:P.patch.Branches K G)(hL:2≤P.L.val)(p r:ℕ)(T:Anthem D G)(v:Studio D): migrates a P V K W ρ h hL p r T v 0=quick P V W T ρ h hL p r v 0:= funext fun _=> paid_nil _ _ _ _ (book_fresh _) (book_guard _)
variable (F:Frame G d)(H:Source.Hol G)(hp:d<D)(Y: Roof.Plaza F D)(hy:Court o F Y)
variable (P:Flight j u)(V:Lodge P.patch){K:KernelChoices}(h:P.patch.Branches K G)(W:Pot G)(hW:Story W (pink K.penalty P.wing))(ρ:ChartRatio G)(hρ:LocalRatio ρ)(hK:4≤u)(hd:d≤j)(hL:2≤P.L.val)(a:hue G)
include H hy hW hρ hK hd hp
lemma migration (T:Anthem D G)(hx: Clef o T l)(m:ℕ)(hm:l≤ m):
   let G:= migrates a P V K W ρ h hL d; let U:=pTrain F ρ a P V h hL W Y
   clover F P.land K.penalty (G m T) l = noncontract F U *ᵥ clover F P.wing K.penalty T l:= by
    intro G' U; funext i
    let M:=clover F P.wing K.penalty T l
    let s:=slots F i;obtain ⟨Z,HZ,PZ⟩:=completed P.wing K.penalty_pos P.legal (from_clef hx 0) s
    have he: clover F P.land K.penalty (G' m T) l i=coeff 0 (echo F (G' s Z) i):= by
       let p:=Pose.inside F i D;rw [echo_nil]; apply congr_arg (fun t=>pearlJ F (r:=s) t (mint F i)); change pageant (bandP _ _ _) ((G' m T) p 0) _ _=G' _ Z p 0 _; unfold G'; rw [mood_nil,quick_more P V ρ h hρ hW.toVivid hx.fare hL m hm,mood_nil]; exact angels o P V h W ρ hW hK hρ hL (from_clef hx 0) HZ.fare PZ p d
    let S:=Finset.univ.filter (fun j:Letter F=> slots F j=s)
    have hS j: j∈S↔ slots F j=s := by simp only [S,Finset.mem_filter,Finset.mem_univ, true_and]
    have hZ j (h:j∈ S): coeff 0 (echo F Z j)=M j:= by rw [echo_nil]; apply congr_arg (fun z=>pearlJ F z (mint F j)); rw [hS] at h; rw [h]; exact PZ _
    let X:=∑ j ∈S,launch (C (M j)) (Y j)
    have hc j (h : j∈ S): Clef o (Y j) s:= (hS j).mp h ▸ hy.officers _
    have hc' j (h : j∈ S): Clef o (launch (C (M j)) (Y j)) s:= (hc _ h).launch _
    have hu: Clef o X s:= Clef.sum S _ hc'
    have hx' j (hh:slots F j=slots F i) : coeff 0 (echo F (Z-X) j)=0:= by
        rw [Clover.chalk_less F j hu.fare HZ.fare,map_sub,hZ j ((hS _).mpr hh)];unfold X; rw [(echo_tally F S _ (fun i hi=>(hc' i hi).fare) j).2]; rw [Finset.sum_eq_single j,etched_launch F _ (hc j ((hS _).mpr hh)).fare, hy.city j j, if_pos rfl,mul_one]; simp
        · intro k hk H; rw [etched_launch F _ (hc k hk).fare, hy.city j k, if_neg (Ne.symm H),mul_zero]
        exact fun h=> False.elim (h ((hS _).mpr hh))
    have hQ:= tip_top F ρ a P V h hL hd hK H W (Z-X) i (HZ.sub hu) d (fun j _=> hx' j) hp le_rfl hW.toVivid hρ (Pose.weightFits F i) s
    have hv : G' s (Z-X)=G' s Z-G' s X := by apply eq_sub_of_add_eq; unfold G'; rw [←migrate_add a h hL d (HZ.fare.sub hu.fare) hu.fare hW hK hρ le_rfl,sub_add_cancel]
    change coeff 0 (echo F (G' s (Z-X)) i)=_ at hQ; rw [hx' i rfl,mul_zero, hv,Clover.chalk_less F i (migrate_w a h hL _ hu hW hK hρ le_rfl).fare (migrate_w a h hL _ HZ hW hK hρ le_rfl).fare,map_sub] at hQ
    rw [he,sub_eq_zero.mp hQ];unfold X;rw [tally _ _ P V h hL W o S _ (fun i hi=>(hc' i hi).fare) hW hK hρ d]; rw [(echo_tally F S _ (fun i hi=>(migrate_w a h hL _ (hc' i hi) hW hK hρ (l:=s) le_rfl).fare) i).2,map_sum]; symm; unfold Matrix.mulVec dotProduct; rw [←Finset.sum_subset (Finset.subset_univ S) (?_)]
    · refine Finset.sum_congr rfl fun j hj=>?_ ; have hvj:= (hS j).mp hj; change noncontract F U i j * M j=_; rw [show noncontract F U i j=_ from (if_pos (show Pose.slots F i=Pose.slots F j from hvj.symm): noncontract F U i j=coeff 0 (U i j)), migrate_plus (Y:=Y j) a h hL _ _ (hc _ hj).fare hW hK hρ le_rfl,etched_launch F _ (migrate_w a h hL _ (hc j hj) hW hK hρ le_rfl).fare, rele,subst_C]
      change coeff 0 (echo F (G' d (Y j)) i)*_=coeff 0 (PowerSeries.C (M j)*_); unfold G'; rw [coeff_C_mul, mul_comm]; unfold migrates; rw [quick_more P V ρ h hρ hW.toVivid (hc j hj).fare hL d (slotsFits F i)]
    intro w _ hw; change noncontract F U i w * M w=0; rw [show noncontract F U i w=0 from if_neg (show Pose.slots F i≠Pose.slots F w from Ne.symm ((hS w).not.mp hw)),zero_mul]
end YM.FormalBulk08.Avenue
