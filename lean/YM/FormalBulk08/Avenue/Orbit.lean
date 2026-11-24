import YM.FormalBulk08.Avenue.Ward
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
-- exact Kalm & cream for any test mark at leading
open City PowerSeries
open Roof Wine Source Source.Drops Labels
variable {o:Loc G 1} {d:ℕ}
open Trellis Aster Dove Quire Clover Elm North
open Dove.Lab
variable {I:Type}{K:KernelChoices}{W:Lab G K I}
section
variable {V:Type*} [Fintype V] [DecidableEq V] {M:Matrix V V ℝ}{s w:V→ℕ}{b:V→ℝ}
abbrev tag (M:Matrix V V ℝ) := (C (R:=ℝ)).mapMatrix M
lemma tagBack (h:Found s w (tag M) b): IsUnit M.det ∧ tag M⁻¹=(tag M)⁻¹ := by
   have hu: IsUnit M.det:= by
      have hv:=voucher h
      rw [tag,←RingHom.map_det,PowerSeries.isUnit_iff_constantCoeff, constantCoeff_C] at hv; exact hv
   refine ⟨hu,left_inv_eq_right_inv (?_ : tag (M⁻¹) * (tag M)=1) (Matrix.mul_nonsing_inv _ (voucher h))⟩
   rw [tag,tag, ←_root_.map_mul,Matrix.nonsing_inv_mul _ hu, map_one]
lemma unitFound (A: V→ℕ)(T:Matrix V V ℝ)(h:∀ i j, A j≤ A i → T i j=if i=j then 1 else 0): Found A A (tag T) 1:= by
    constructor
    · intro i j he; rw [show coeff 0 (tag T i j)=T i j from coeff_zero_C _,h _ _ he.le,if_neg (fun (e:i=j)=>Nat.lt_irrefl (A i) (e.symm ▸ he))]
    · exact fun _=>one_pos
    intro i j hp _; change coeff 0 (C _) = _; rw [coeff_zero_C,h i j hp.ge];rfl
end
variable {E R:ℕ}{ρ:ChartRatio G}{F:Frame G d}{T:SectionData F}{H:Source.Hol G}
variable (h:Use W ρ E)(q:Quota F H W o D E R)(v:LocalRatio ρ)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)(hR:d≤R)(u: Extras W) (a:hue G)
include h q v hs ht hb hR u a
lemma struckW (x:Leaf W.scrolls)(i j:Letter F) : Ends (fun m=> WLocal W a ρ F T q.horizon x m i j) (WLimit W a ρ F T q.horizon x i j):= by
    let f n : meshPoint W:= ⟨x, n+x.b,n+x.b,by omega,le_rfl⟩; refine (tendsto_add_atTop_iff_nat x.b).1 (quietP (δ:=fun n=>fare_n x (n+x.b)) ?_ (fun i=> (ratioR_pos ..).le) ?_); · exact (tendsto_add_atTop_iff_nat x.b).mpr (fare_fin x)
    apply Pact_lift (g:=f) _ (patrons h q v hs ht hb hR u a i j) (fun _=>le_refl _); exact soft_coin _ (chron W.scrolls |>.day x)
omit h u hR in
lemma towerF (x:Leaf W.scrolls)(i) (hi:x.b≤ i): Found (Pose.slots F) (Pose.slots F) (tag (WLocal W a ρ F T q.horizon x i)) 1:= unitFound (Pose.slots F) _ (woven_diagonal (location _ _ _) K.penalty_pos ((W.V x.a).clock.adm x.b) (birth a v q hs ht hb x.a x.b i x.zone hi)) -- `K:`
lemma summitF (x:Leaf W.scrolls) : Found (Pose.slots F) (Pose.slots F) (tag (WLimit W a ρ F T q.horizon x)) 1:= by
    apply unitFound; intro i j hh; refine tendsto_nhds_unique (struckW h q v hs ht hb hR u a x i j) (tendsto_const_nhds.congr' ?_); filter_upwards [eventually_ge_atTop x.b] with k hk; exact (woven_diagonal _ K.penalty_pos ((W.V x.a).clock.adm x.b) (birth a v q hs ht hb x.a x.b k x.zone hk) i j hh).symm
lemma receiveW (x y:Letter F): Pact (aurum W) (purseR targetPower) (fun z=>(WLocal W a ρ F T q.horizon z.toLeaf z.top)⁻¹ x y) (fun z=> (WLimit W a ρ F T q.horizon z.toLeaf)⁻¹ x y):= by
    have he (z:meshPoint W):=towerF q v hs ht hb a z.toLeaf z.top z.wing; have hx (z:meshPoint W):= summitF h q v hs ht hb hR u a z.toLeaf
    have hp(i j:Letter F):Priced (aurum W) (purseR targetPower) (fun z=>tag (WLocal W a ρ F T q.horizon z.toLeaf z.top) i j) (fun z=> tag (WLimit W a ρ F T q.horizon z.toLeaf) i j) 0:= by
       intro t ht'; replace ht':t=0:=by omega
       subst t; simp_rw [tag, RingHom.mapMatrix_apply, Matrix.map_apply, coeff_zero_C]; exact patrons h q v hs ht hb hR u a i j
    have ht:= prize_back he hx (fun i=>soft_coin _ (1:ℝ)⁻¹) hp x y 0 (Nat.zero_le _); simp_rw [←(tagBack (he _)).2,← (tagBack (hx _)).2,tag, RingHom.mapMatrix_apply, Matrix.map_apply, coeff_zero_C] at ht; exact ht
set_option maxHeartbeats 1000000 in
lemma wallspring (x:Leaf W.scrolls):
   let U:= Drift.tableau F a ρ T q.horizon x
   WLimit W a ρ F T q.horizon x * preTable U=noncontract F U * WLimit W a ρ F T q.horizon (porch x):= by
   intro U; let G' N:= WLocal W a ρ F T q.horizon x (seqN x N); let X N:= WLocal W a ρ F T q.horizon (porch x) (seqN x N); let F' N:= bornM (T:=T) (W:=W) (ρ:=ρ) a q.horizon x.a (seqN x N) x.b
   have he n: G' n*preTable (F' n)=noncontract F (F' n)* X n:= by
       let i:=x.b; let P:= W.V x.a; let N:=seqN x n
       have hp:i<N:=by unfold i N seqN; omega
       let Q:= destination P N i;let M:=bornY ρ W a F T q.horizon x.a N (i+1);let Z:= W.wood x.a i;let S:=Lab.saga ρ a W x.a N (i+1)
       have ht':Story S (pink K.penalty Q.wing):= (genu P (W.wood x.a) (W.toEmpire.bill x.a) ρ a v hs hp).toStory;have hj:D>d:= q.horizon
       have hk:= wallpaper F H hj o ρ a Q Z (W.toEmpire.bill _ _) S ht' v (P.clock.adm _) (quota_fits q x) (growL _ _) M (birth a v q hs ht hb x.a (i+1) N (x.zone.trans (Nat.le_succ _)) hp)
       change Woven F (location (W.V x.a) N i) _ (bornY _ _ _ _ _ _ x.a N i) * preTable _= _; rw [born_walk a q _ _ _ hp];unfold P Q at *; rw [loc_land _ _ _ hp]; exact hk
   have hv:Tendsto (seqN x) atTop atTop:= tendsto_atTop.mpr fun i=> (eventually_ge_atTop i).mono (fun k hk=>by unfold seqN;omega)
   ext i j; have hP(p v':Letter F) : Ends (fun n=> noncontract F (F' n) p v') (noncontract F U p v') := by
       unfold noncontract;split; exact orig q h v a hs ht hb hR x p v' (Nat.zero_le E) -- left also if
       exact tendsto_const_nhds
   have hp(p:Letter F):= (struckW h q v hs ht hb hR u a x i p).comp hv
   have h₁:Tendsto (fun n=>(G' n*preTable (F' n)) i j) atTop (𝓝 ((WLimit W a ρ F T q.horizon x * preTable U) i j)):= by
       simp_rw [Matrix.mul_apply]; exact tendsto_finsetSum _ (fun i _=> (hp i).mul (Trellis.orig q h v a hs ht hb hR x i j (Nat.zero_le E)))
   refine tendsto_nhds_unique h₁ (?_); simp_rw [he,Matrix.mul_apply]; exact tendsto_finsetSum _ fun p _=> (hP i p).mul ((struckW h q v hs ht hb hR u a (porch x) p j).comp hv)
end YM.FormalBulk08.Avenue
