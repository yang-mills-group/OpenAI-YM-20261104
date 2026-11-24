import YM.WilsonCoeffUV.Wick.Source
/-! # The precise Wick intertwiner on master coords (no Gram quotient yet)
Horizon h smoothing supplies require structural license. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Exterior Next.Free Tree Precision Power Embroider Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm Fountain
open Bank.Carp
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {c f n:Side}{U V α:Type*} {G:Gauge} {h D i j k e n' m N r:ℕ}{F:Labels.Frame G h} {H:Hol G}
variable {z ξ σ A' B:ℝ} {s t:ℝ}

def identum (A:Wall F):Wall F:=of fun i j=> if valence F i=valence F j then A i j else 0
lemma panel_rect {P:Patch}{J:Drip P G}(u:h ≤ k)(Z:ChamberTen G (Vote D) r): hall P k J Z=(P.L.val:ℝ)^(k-h) • hall P h J Z:=by rw [hall,hall,smul_smul,tiara,tiara, ← mul_div_assoc,← pow_add, Nat.sub_add_cancel u]
lemma hall_scale (P:Patch)(T:Drip P G)(x:ℝ)(Y:ChamberTen G (Vote D) r): hall P k T (x•Y)=x•hall P k T Y:=by
   have he w:pulseS P w T (x•Y)= x • pulseS P w T Y:= by
       funext i; unfold pulseS pump; rw [Pi.smul_apply,← tsum_const_smul'']; apply tsum_congr; intro j; apply (congr_arg _ (show featherS P w (x • Y) j=x • featherS P w Y j from map_smul (soprano P w D) x _)).trans; exact smul_comm ..
   unfold hall; simp_rw [he, ← Finset.smul_sum]; rw [smul_comm]
lemma hall_norm (P:Patch)(J:Drip P G)(K:Finset U)(Y:U→ChamberTen G (Vote D) r)(p:dragCup Bank.terrain s B J)(q:0<s)(t:∀ i∈ K,Hedged (Y i))(k):
   (∀ i∈K, Standby (hall P k J (Y i)))∧ hall P k J (∑ i∈K,Y i)=∑ i∈ K,hall P k J (Y i):=by
    classical
    have tt(Y:ChamberTen G (Vote D) r) (h:Hedged Y) : Standby (hall P k J Y):=by
       obtain ⟨r,C,u,hr⟩:= h.tax; set v:=min r s; have he:=lt_min u q
       exact ⟨v/2,_,half_pos he,hall_fares _ _ (p.mono (min_le_right ..)) _ _ hr ((div_le_self he.le (by exact_mod_cast P.L.property)).trans (min_le_left ..)) (half_pos he).le (half_lt_self he)⟩
    refine ⟨fun i h=>tt _ (t i h),?_⟩
    induction K using Finset.induction_on with
    | empty=> rw [Finset.sum_empty, Finset.sum_empty]; funext i; simp [hall,pulseS,pump,spinJob,featherS,revolve]
    | insert i v hi ih=>
       have ht:∀ i∈v,Hedged (Y i):= fun j hj=>t j (Finset.mem_insert_of_mem hj)
       let U:=∑ i∈v,Y i; let H:= Y i+U; have he:= t i (Finset.mem_insert_self ..)
       have hx:= Hedged.pooled v ht
       obtain ⟨u,A,hU,hA⟩:=(Hedged.plus he hx).tax
       obtain ⟨g,B',hB,hB'⟩:=hx.tax; set C:= max A B'; let d:= min u g; have hd:=lt_min hU hB; set x:=min s d; have hv:= lt_min q hd; have hQ:Twig 0 d C H:= Cork.cost (Cork.mono hA (min_le_left ..)) (le_max_left ..)
       rw [Finset.sum_insert hi,Finset.sum_insert hi, ← ih ht]; change hall P k J H= _; apply eq_add_of_sub_eq;
       have hp:= hall_diff P J (p.mono (min_le_left ..)) H U hQ (Cork.cost (Cork.mono hB' (min_le_right ..)) (le_max_right ..)) hv ((div_le_self hv.le (by exact_mod_cast P.L.property)).trans (min_le_right ..)) k
       rw [show H-U= Y i from by unfold H; abel] at hp; exact hp.symm

lemma rough_lane (Y:Single G D)(P:Estate G D)(u:Solo k P Y)(r): Hedged (Y 0 r):=
  ⟨solo_mural u r 0, solo_pure u 0 r, solo_stretch u .., wing_c (P:=Y 0) (fun i x j=>sky_split (solo_upright u) (solo_pure u) 0 i (by intro _ h; omega) x j) r⟩
variable {I:Cloister G h}
lemma scoop_F (P:Island F D)(p:Shimmer P)(Q:Stand (inkPin I))(T:Courant I Q)(t:h<D)(u:dragCup Bank.terrain s B Q.Q)(he:0<s)(H:Hol G)(i:Alma F)(Y:ChamberTen G (Vote D) (valence F i))(v:Hedged Y): let R:=prismata F (legion Q P.2)
    echoS F (hall (inkPin I).patch h Q.Q Y) i = ∑ j,identum (lineS R 0) i j* echoS F Y j :=by
    intro R; let K:= (inkPin I).patch
    let S:= blockS F (valence F i)
    let b(j:Alma F) := P.2 j 0 (valence F i); let g:=echoS F Y
    let M(j:Alma F):= g j • b j; let A:=∑ j∈ S,M j
    have hB j: Hedged (b j):=rough_lane _ _ (p.scan.solo j) _; have hM j:Hedged (M j):=Hedged.loom (hB j) (g j); have hA:Hedged A:= Hedged.pooled S (fun j _=>hM j)
    have hh : Hears F h 0 (Y-A):= by
       obtain ⟨a,b',he,h'⟩:= v.tax; obtain ⟨s,b'',hv,hv'⟩:=hA.tax; refine ⟨le_rfl,fun j _ ht=>?_⟩; rw [echo_minus _ _ h' hv' he hv]; change ‖g j-echoS F A j‖≤0; apply norm_le_zero_iff.mpr; unfold A; rw [echo_sum _ _ _ (fun i _=> (hM i).tax),Finset.sum_eq_single_of_mem j (show j∈ S from Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩)]
       · rw [show echoS F (M j) j=g j* echoS F (b j) j from echo_mu F .., show echoS F (b j) j=1 from ?_,mul_one,sub_self]; rw [← show glean F _ 0 j= _ from (by rw [g_lone,ht]: glean F (P.2 j) 0 j= echoS F (b j) j),epoch p]; simp
       intro l hL hl; rw [show echoS F (M l) j=g l * echoS F (b l) j from echo_mu F ..,show echoS F (b l) j=0 from ?_,mul_zero]; rw [← show glean F _ 0 j= _ from (by rw [g_lone,ht]: glean F (P.2 l) 0 j= echoS F (b l) j),epoch p]; simp [hl]
    rw [visibleN (I:=I) (T:=Q) (P:=Y) v hA T hh t H u he];
    obtain ⟨hf,hg⟩:=hall_norm K _ S M u he (fun i _=>hM i) h
    change echoS F (hall K h Q.Q (∑ j∈ S,M j)) i= ∑ j,identum (lineS R 0) i j*g j
    rw [hg,echo_sum F i _ hf]
    apply Eq.trans (b:=∑ j∈ S,identum (lineS R 0) i j * g j)
    swap
    · exact Finset.sum_subset (Finset.subset_univ _) (fun j _ hj=>by rw [identum,Matrix.of_apply,if_neg (fun v=>hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,v.symm⟩)),zero_mul])
    apply Finset.sum_congr rfl; intro j hj; have hz : valence F i=valence F j := (Finset.mem_filter.mp hj).2.symm
    unfold M; rw [hall_scale K Q.Q,echo_mu F]; unfold identum; rw [Matrix.of_apply,if_pos hz]; change g j*echoS F (hall _ _ _ _) i=lineS _ _ _ _ * _; rw [mul_comm (g j)]; apply congr_arg (· * g j); unfold R; rw [coined,Cosmos.g_lone]; unfold b; rw [hz]; change _=echoS F (fanfare (inkPin I) Q h (P.2 j) 0 (valence F j)) i; rw [fanLead (inkPin I) Q h (P.2 j) (streams p j).born]
end YM.WilsonCoeffUV.Cosmos
