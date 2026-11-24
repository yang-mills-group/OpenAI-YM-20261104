import YM.Trace.Physicalv2.GermPrices

/-!
Numerics for stable descent on a single live trajectory. Constants here do
not yet price the fresh conditional errors. Keeping a damping exponent larger
than the backfeed buys the unused margin.
-/
noncomputable section
namespace YM.Trace.Physical.GermGraph
open Function Set Filter Labels Lattice Wilson RG Source Analysis Next.Foundations
open Push.Local ProjectorNext.Equivariance MeasureTheory Extra.Histories Relay
open Germ Bid Work.G08 PhysicalNext.Repeat.Lotus YM.MergeProof Motion
open PhysicalNext.Repeat.Legato.Bandage
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 125000
set_option quotPrecheck false
set_option warningAsError false
set_option maxRecDepth 3300
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
variable {G:Gauge}(C:Family G)
local notation "L" => factor C
lemma factor_positive (i:ℕ):1<factor C i:= by exact_mod_cast (lt_of_lt_of_le (by norm_num:(1:ℕ)<3) (C.S.block_large i))
def hike (t i:ℕ)(α:ℝ):= (C.S.a t / C.S.a i)^α
lemma hike_pos (a b:ℕ)(α:ℝ):0< hike C a b α:= Real.rpow_pos_of_pos (div_pos (C.S.a_pos _) (C.S.a_pos _)) _
lemma hike_ge {t i:ℕ}{α:ℝ}(ht : t ≤ i)(ha : 0 ≤ α):1 ≤ hike C t i α:=Real.one_le_rpow ((one_le_div (C.S.a_pos i)).mpr (C.S.strictAnti.antitone ht)) ha
lemma hike_id (t:ℕ)(α:ℝ): hike C t t α=1:= by unfold hike; rw [div_self (C.S.a_pos _).ne', Real.one_rpow]
lemma hike_succ (t i:ℕ)(α:ℝ): hike C t (i+1) α = hike C t i α * L i ^ α := by
   have he: C.S.a t / C.S.a (i+1) = (C.S.a t / C.S.a i)* L i:=by rw [C.S.a_step]; change C.S.a t / (C.S.a i / ((C.S.block i).val:ℝ)) = (C.S.a t/C.S.a i)*((C.S.block i).val : ℝ); field_simp [(C.S.a_pos i).ne',show (↑(C.S.block i).val:ℝ)≠0 by have := factor_positive C i; exact ne_of_gt (zero_lt_one.trans this)]
   unfold hike; rw [he, Real.mul_rpow (div_nonneg (C.S.a_pos _).le (C.S.a_pos _).le) (by exact (zero_lt_one.trans (factor_positive C i)).le)]
lemma hike_back (t i:ℕ)(α:ℝ):hike C t i α = (L i)^(-α) * hike C t (i+1) α:= by
   have he:=hike_succ C t i α; have hl := factor_positive C i
   rw [he,Real.rpow_neg (zero_lt_one.trans hl).le]
   have hp:0<L i^α:=Real.rpow_pos_of_pos (zero_lt_one.trans hl) _
   field_simp
local notation "U" => (fun t i=>hike C t i rate)
local notation "q" => (fun m=>L m^(-rate))
local notation "v" => (fun m (γ:ℝ)=>L m^γ)
lemma factor_cap {γ:ℝ}(hγ:0≤γ)(hr:γ<rate) : ∀ᶠ t:ℕ in atTop, ∀ m≥t, q m ≤1/2 ∧ q m * v m γ ≤ 1/2 :=by
   have ht : Tendsto (L) atTop atTop:=tendsto_atTop.2 (fun a=> by
      let b:=max 1 a
      have hb:0<b:=zero_lt_one.trans_le (le_max_left ..)
      filter_upwards [factor_large C b⁻¹ (inv_pos.mpr hb)] with i hi; exact le_trans (le_max_right ..) (inv_inv b ▸ hi.1))
   have hz:(rate-γ)>0:= sub_pos.mpr hr
   obtain ⟨n,hn⟩:=eventually_atTop.mp (((tendsto_rpow_neg_atTop hz).comp ht).eventually (gt_mem_nhds (by norm_num:(0:ℝ)<1/2)))
   filter_upwards [eventually_ge_atTop n] with t hh m hi
   have hl := factor_positive C m
   have hp₀ :0 ≤ q m:= Real.rpow_nonneg (zero_lt_one.trans hl).le _
   have hq := le_of_lt (hn m (hh.trans hi))
   have ht: q m * v m γ = L m ^(-(rate-γ)):=by rw [←Real.rpow_add (zero_lt_one.trans hl)]; congr 1; ring
   exact ⟨(le_mul_of_one_le_right hp₀ (Real.one_le_rpow hl.le hγ)).trans (ht.trans_le hq),ht.trans_le hq⟩

lemma down_est {t top:ℕ}{r:ℕ→ℝ}{D:ℝ} (hTop:t≤top)(hr:0≤r top)(hD:0≤D)(hL:∀ m≥t, q m ≤ 1/2) (h:∀ m≥t, m<top→ r m ≤ q m * r (m+1)+D) : ∀ i≥t, i≤top → r i ≤ U top i * r top + 2*D:=by
    intro i ht hi
    induction hi using Nat.decreasingInduction with
    | self => change _ ≤ hike C top top _ * _ + _; rw [hike_id,one_mul]; linarith
    | of_succ m hm ih =>
       have hl := factor_positive C m
       have hq₀:0≤q m:=Real.rpow_nonneg (zero_lt_one.trans hl).le _
       refine (h m ht hm).trans ((add_le_add (mul_le_mul_of_nonneg_left (ih (ht.trans m.le_succ)) hq₀) le_rfl).trans ?_)
       change _ ≤ hike C top m _ * _ + _; rw [hike_back C top m]
       have hz := mul_le_mul_of_nonneg_right (hL m ht) hD
       nlinarith only [hz]

lemma across_est {t top:ℕ}{r X:ℕ→ℝ}{D γ ε b:ℝ}(hγ:0≤γ) (hTop:t≤top)(hr:0≤r top)(hε:0≤ε)(hε':ε≤1)(hD:0≤D)
    (hL:∀ m≥t, q m ≤1/2 ∧ q m * v m γ ≤ 1/2)
    (h:∀ m≥t, m<top→ r m ≤ q m * r (m+1)+D ∧ X (m+1) ≤ v m γ*(X m + ε*q m*r (m+1)+D)) (hb:X t ≤ b):
     (∀ i≥t,i≤top → r i ≤ U top i * r top+2*D) ∧ ∀ i≥t,i≤top→ X i ≤ hike C t i γ*(b+2*((i:ℝ)-t)*D)+2*ε*U top i*r top:=by
   have hd:=down_est C hTop hr hD (fun m hm=> (hL m hm).1) (fun m hm hy=> (h m hm hy).1)
   refine ⟨hd,?_⟩
   intro i hi hr'
   induction i, hi using Nat.le_induction with
   | base=>rw [show (↑t:ℝ)-↑t=0 from sub_self _]; simp only [mul_zero,zero_mul,add_zero,hike_id,one_mul]; have := mul_nonneg (mul_nonneg (mul_nonneg (show (0:ℝ)≤2 by norm_num) hε) (hike_pos C top t rate).le) hr; linarith
   | succ i hi ih=>
      have ht':i < top:=hr'
      have hv:= (hL i hi)
      have hl:= factor_positive C i
      let c := L i ^(-rate)
      let a := L i^γ
      let u:= U top
      have ha:0<a:=Real.rpow_pos_of_pos (zero_lt_one.trans hl) _
      have hc:0< c:=Real.rpow_pos_of_pos (zero_lt_one.trans hl) _
      have he : ε * c ≤ 1/2:= (mul_le_mul hε' hv.1 hc.le zero_le_one).trans_eq (one_mul _)
      have hz : u i = c*u (i+1):=hike_back C top i rate
      have hcq := mul_le_mul_of_nonneg_left (hd (i+1) (hi.trans i.le_succ) hr') (mul_nonneg hε (show 0≤q i from hc.le))
      have hpaid : ε*q i*r (i+1) ≤ ε*u i*r top + D:=by
        refine hcq.trans ?_
        change ε*c*(u (i+1)*r top + _) ≤ _
        rw [hz]; nlinarith only [mul_le_mul_of_nonneg_right he (show 0≤ D from hD)]
      have hs : 3*(ε*u i*r top)*a ≤ 2*(ε*u (i+1)*r top):=by
          have hnn:=mul_nonneg (mul_nonneg hε (hike_pos C top (i+1) rate).le) hr
          change _ ∧ c*a ≤ _ at hv
          have hh := mul_le_mul_of_nonneg_right hv.2 hnn
          rw [hz]; nlinarith only [hh,hnn]
      refine (h i hi hr').2.trans ((mul_le_mul_of_nonneg_left (add_le_add (add_le_add (ih ht'.le) hpaid) (le_refl _)) ha.le).trans ?_)
      change a*(hike C t i γ*_ +2*ε*u i*r top+(ε*u i*r top+D)+D) ≤ hike C t (i+1) γ*_+2*ε*u (i+1)*r top
      rw [hike_succ C t i γ,Nat.cast_add,Nat.cast_one]
      have hbudget : a*(2*D) ≤ hike C t i γ*a*(2*D):=mul_le_mul_of_nonneg_right (le_mul_of_one_le_left ha.le (hike_ge C hi hγ)) (by linarith only [hD])
      change _ ≤ hike C t i γ*a*_ + _
      nlinarith only [hbudget,hs]
end YM.Trace.Physical.GermGraph
