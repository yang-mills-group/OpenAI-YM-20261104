import YM.OPE.Pulse.Regroup
import YM.OPE.Sweep.Join
/-!
# Regroup, keeping ungrouped lanes, one step. Paying an exponent allowance
for the extra Respawn in progress. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {Z V I J T : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]
  [Fintype J][DecidableEq J]{G:Gauge}{n:Side}
variable {A:History G}{N p k i j:ℕ}
    {δ φ σ χ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (A.rep N p (m+1)) (A.rep N p m)}
    {E: V→Site (A.S.side i p)}{P:V→Motion}{v:V}{B:V→Equiv.Perm V}{o:V×I→Site (A.S.side i p)}
set_option quotPrecheck false
local notation "R" => A.rep N p
local notation "Y'" => A.levels.budget
local notation "a" => scurry A.levels r χ (δ i) i
local notation "e" => (Y' i).supportExponent
local notation "Γ" => (Y' i).B
variable {Q:Config G (A.S.side i p)→Poly (Names V I)} {W W':I→ℝ}{c: V×I→ℂ}
variable (H l : ℕ) (L:Fibers I J)

lemma unit_license (hV:ClusterPars A δ χ r i) (he:0<H)(hx:0≤ e): license A δ H l i ≤ δ i:= by
    have hδ := hV.funs; let v:= Real.exp (((Y' i).supportExponent+1/2)*l); have hh:1 ≤ v:= Real.one_le_exp (mul_nonneg (by linarith only [hx]) (by positivity))
    have h:0<δ i/H:= div_pos hδ.1 (by positivity); have h' : δ i/H≤1:= (div_le_self hδ.1.le (by exact_mod_cast he)).trans hδ.2; change _ / v≤_
    exact (div_le_self (mul_nonneg h.le hδ.1.le) hh).trans (mul_le_of_le_one_left hδ.1.le h')
private lemma twice_exp {x:ℝ} (h:0≤x)(he:x≤1): Real.exp x-1≤2*x:= by
    have hx := Real.abs_exp_sub_one_le (show |x|≤1 from (abs_of_nonneg h).trans_le he)
    rwa [abs_of_nonneg h, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp h))] at hx
lemma allowance (h: Duty A r i (δ i) (σ i) (χ i))(hc:0≤χ i)(ht:ClusterPars A δ χ r i):
    let t:= (r i)*siteFactor (A.levels.budget i).B*δ i
    let z := Real.exp (scurry A.levels r χ (δ i) i)-1
    (((A.levels.budget i).B + (A.levels.budget i).B+1:ℕ):ℝ)^4*(z+t) ≤ (A.levels.budget i).supportExponent-((A.levels.budget i).supportExponent-3) ∧ Real.exp (z+t)-1≤1:=by
    intro t z; let x:ℝ:= (((Γ+Γ+1:ℕ):ℝ)^4:ℝ); have hx':(4:ℝ)≤x:=by unfold x; have h := (show 3 ≤ Γ+Γ+1 from by have := (Y' i).B_pos; omega); exact le_trans (by norm_num : (4:ℝ) ≤ 3^4) (pow_le_pow_left₀ (by norm_num) (by exact_mod_cast h) _)
    have hx:1 ≤ x:=le_trans (by norm_num) hx'; have hx0:0 ≤ x:=zero_le_one.trans hx; have hv:0<δ i:= ht.funs.1; have hw:=h.stakes.1; have hu:0 ≤ t:=by unfold t; have hx := extra h; positivity
    have hr:x*t≤1/2:= (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hc) hx0).trans hw
    have he:0≤ a:= by unfold scurry Ribbons.Salt.scent; positivity
    have hz:x*z ≤ 1:= by
       apply (mul_le_mul_of_nonneg_left (twice_exp he ?_) hx0).trans; swap; · exact (le_mul_of_one_le_left he hx).trans (ht.bars.1.trans (by norm_num))
       have he : x*a ≤ 1/2 := ht.bars.1; linarith only [he]
    have hv:z+t ≤ 1/2:= by
       have h :0≤z:= sub_nonneg.mpr (Real.one_le_exp he)
       nlinarith only [mul_le_mul_of_nonneg_right hx' (add_nonneg h hu),hr,hz]
    exact ⟨by change x*_≤_; linarith only [hr,hz],(twice_exp (add_nonneg (sub_nonneg.mpr (Real.one_le_exp he)) hu) (hv.trans (by norm_num))).trans (by linarith only [hv])⟩
where extra (h: Duty A r i (δ i) (σ i) (χ i)): 0≤ siteFactor (A.levels.budget i).B:= by unfold siteFactor; positivity
local notation "Q'"=> (fun U=> Fibers.reap (partialGroup V L) (Q U))
local notation "o'"=> (o ∘ (partialGroup V L).twig)
local notation "W₀"=> (grouped A δ H l i W L)
variable {g:V×I→ Config G (A.S.side i p)→ℂ} {K:V×I→ℕ→ Config G (A.S.side i p)→ℂ}
lemma regroups (h:A.Selected)(hn:i≤N)(hr:ClusterPars A δ χ r i)(hD:Duty A r i (δ i) (σ i) (χ i))
    (hc:Arc (R i) g K Q v P E B o (fun j=>δ i*W j.2) ((A.levels.budget i).supportExponent+1/2) ((A.levels.budget i).supportExponent+1) 1 (χ i) (δ i) c)
    (hB: ∀ x,Dominated (K x))(hp:May v P E B g (fun x=> profile (A.rep N p i).activities (K x)) c)(hP:∀ j U,(Q U).part ((Names V I).fire j)=coin (R i) (g j) (K j) U)
    (hΩ:∀ j,j≠v→∀ b:I,o (j,b)=affine (P j).1 (E j) (o (v,b)))
    (C:J→Prop) (hξ:∀ j,C j→L.Only j) (hw:∀ j,0<W j)(hy:∀ x,W x.2*‖c x‖≤1)
    (hs:Arsenal (A.rep N p i)) (hH:0<H)(hF:Fintype.card I ≤ H) (hO:Occupancy o (r i))
    (hS:∀ j:V×I, coverNumber (A.levels.budget i).B ({o (j.1,L.twig (L.bunch j.2)),o j}:Support _) ≤ l) :
    ∃ (g':V×J→ Config G (A.S.side i p)→ℂ) (K':V×J→ℕ→ Config G (A.S.side i p)→ℂ),
       (∀ j,C j.2→ g' j=g (j.1,L.twig j.2) ∧ K' j=K (j.1,L.twig j.2)) ∧ (∀ j,¬ C j.2 → Blade (R i) (o' j) (g' j) (profile (A.rep N p i).activities (K' j)) 0 (4*(1/grouped A δ H l i W L j.2))) ∧
       (∀ j,Dominated (K' j)) ∧ May v P E B g' (fun j=> profile (A.rep N p i).activities (K' j)) 0 ∧ Serves (R i) g' (fun j=> profile (A.rep N p i).activities (K' j)) Q' v P E B o' (fun j=> grouped A δ H l i W L j.2) ((A.levels.budget i).supportExponent-3) 1:=by
    have hA:=h.represents N p i hn; have hit:= fun U=>(Tour.bright A h N p i hn U).ne'; have hc0:0≤χ i:= by obtain ⟨_,z,ψ,hζ,h,-,p,-⟩:=hc.see; obtain ⟨s,hs,hV,hT⟩:=p; exact (tsum_nonneg (hV 0).1).trans (hV 0).2.2
    let w(j:V×I):=δ i*W j.snd; let w'(j:V×J):=grouped A δ H l i W L j.snd; let y:=Real.exp a-1; have hδ:=hr.funs
    have hw'(j:V×J):0 < w' j:= grouped_pos H l L hδ.1 hH hw _
    have hξ' (x:V×J) (he:C x.snd): w' x≤ w ((partialGroup V L).twig x):=by
       unfold w' grouped; rw [(show L.contents x.2 = {L.twig x.2} from hξ x.2 he),prod_singleton]
       exact mul_le_mul_of_nonneg_right (unit_license H l hr hH (hA.vac ▸ (R i|>.p.exponent_pos.le))) (hw _|>.le)
    obtain ⟨f',k',hM,hv,hZ,hT,hY,hR⟩:= repriced (Z:=y) L (r i) l H C hs hp hΩ hA.good.labels (hA.vac.symm ▸ hc) hB hP hξ (fun x=>mul_pos hδ.1 (hw x.2)) hw' hξ' hO zero_le_one (fun j=>(mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (hw _|>.le) hδ.2) (norm_nonneg _)).trans (hy _)) hδ.1 hδ.2 (by norm_num) (by norm_num) hδ.1.le hH (cardinal_le H L hF) (hA.vac.symm ▸ hS) hit (hA.vac.symm ▸ grouped_b H l L) (hA.vac.symm ▸ hr.bars.1) (hA.vac.symm ▸ (le_rfl : y≤y)) (by rw [hA.vac]; linarith only : e-3≤(R i).p.supportExponent)
    have hg:Occupancy o' (r i):=by
       intro x; let t:= univ.filter fun j=> o' j=x; have hs:t.image (partialGroup V L).twig ⊆ univ.filter (fun i=>o i=x):= by intro i hi; obtain ⟨j,hj,rfl⟩:=mem_image.mp hi; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hj).2⟩
       exact le_trans (ge_of_eq (Finset.card_image_of_injective _ (partialGroup V L).sectioned.injective)) ((card_le_card hs).trans (hO x))
    have he := allowance hD hc0 hr
    refine ⟨f',k',fun j=>hM j,fun j hj=> (hv j hj).more (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hr.bars.2 (hw' j|>.le)) (by norm_num)),hZ,fun i hi=> ⟨(hY i hi).1,fun j=>⟨((hY i hi).2 j).1, ((hY i hi).2 j).2.1,(scalar_z _).symm⟩⟩,?_⟩
    exact thru (ζ:=0) («Z»:=1) (by rw [add_zero]; exact hR) hA.good.labels hw' hδ.1.le hg (by linarith only [hD.exp.1]) (by rw [hA.vac,add_zero]; exact he.1) hw' (slighter hw' hw' (fun i=> (one_mul (w' i)).symm.le) zero_le_one le_rfl) zero_le_one (by rw [one_mul]; exact hr.bars.2) (by rw [hA.vac,one_mul]; exact he.2) hT hZ hit
end YM.MergeProof.Ribbons.ManyCopies
