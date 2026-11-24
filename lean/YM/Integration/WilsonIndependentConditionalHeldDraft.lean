import YM.Integration.WilsonIndependentConditionalRawVacuum
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Exponential

/-! Vacuum tensors have translation symmetry. Gaussian prediction supplies the summable row for each held coordinate. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalHeldDraft
open Filter Function Matrix Lattice Laurent Bloch RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Soil
open WilsonIndependentConditionalDraftRows
open scoped Classical BigOperators Topology
variable {I:Type}{K:Layer I I}{r:ℕ}{T:Packet I r}

theorem funded (rows:∀x,Summable (fun y=>‖K x y‖)){C:ℝ}(income:∀z,‖T z‖≤C)
    (s:Finset (Fin r))(x:Tuple I r):Summable (fun y=>wires K s x y*T y):=by
  classical
  let W (i:Fin r)(y:I):ℝ:=if i∈s then K (x i) y else if y=x i then 1 else 0
  have pay (i):Summable (fun y=>‖W i y‖):=by
    by_cases hi:i∈s
    · simpa only [W,if_pos hi] using rows (x i)
    apply summable_of_ne_finset_zero (s:={x i})
    intro y hy
    have ne:y≠x i:=by simpa using hy
    simp only [W,if_neg hi,if_neg ne,norm_zero]
  have all:= (YM.Push.LogIdentity.pi_series (Fin r) W pay).1
  apply Summable.of_norm_bounded (all.mul_right C)
  intro y
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (income y) (norm_nonneg _)

theorem expanded (pays:∀s x,Summable (fun y=>wires K s x y*T y))
    (l:List (Fin r))(uniq:l.Nodup)(z:Tuple I r):
    drawing T K l z=∑' y,wires K l.toFinset z y*T y:=by
  classical
  induction l generalizing z with
  | nil=>
    simp only [drawing,List.toFinset_nil,empty]
    symm;rw [tsum_eq_single z]
    · simp
    · intro y ne;simp [ne]
  | cons a l ih=>
    obtain ⟨fresh,nodup⟩:=List.nodup_cons.mp uniq
    let W:Tuple I r→ℝ:=fun y=>wires K (insert a l.toFinset) z y*T y
    have cash:Summable W:=pays (insert a l.toFinset) z
    let f:Tuple I r→I:=fun y=>y a
    have leaf (y:I):K (z a) y*(∑' x,wires K l.toFinset (update z a y) x*T x)=
          ∑' x:(f ⁻¹' {y}),W x:=by
      rw [←tsum_mul_left,tsum_subtype]
      apply tsum_congr;intro x
      rw [←mul_assoc,WilsonIndependentConditionalDraftRows.single K (by simpa using fresh)]
      by_cases eq:x a=y
      · simp [eq,W,Set.indicator,f]
      · simp [eq,W,Set.indicator,f]
    simp only [drawing,ray,Packet.swivel,List.toFinset_cons]
    calc
      _=∑' y, ∑' x:(f ⁻¹' {y}),W x:=by
        apply tsum_congr;intro y;rw [ih nodup];exact leaf y
      _=∑' y,W y:=(cash.hasSum.tsum_fiberwise f).tsum_eq

theorem original {α:Type}[Fintype α]{F:(n:Side)→ ropes (Site n) α α}{M:ropes Cover α α}
    (pilot:Pilots F M){P:raw α ℝ r}{V:Ten ℝ (Cloth α) r}(word:Yields P V)(sym:Smooth V):
    draft M V=reflectCut M.transpose V:=by
  classical
  obtain ⟨σ,A,hσ,paid⟩:=pilot.fees
  have row (x:Cloth α):Summable (fun y=>‖M x y‖):=by
    apply ((keys_cost (α:=α) x.1 hσ).2.1.mul_left A).of_nonneg_of_le (fun _=>norm_nonneg _)
    intro y
    rw [Real.norm_eq_abs]
    apply le_of_tendsto (pilot.point x y).abs
    filter_upwards [paid,now_gap x.1 y.1] with n hn hgap
    have edge:|F n (foldUnder n x) (foldUnder n y)|≤A*Real.exp (-σ*(tor n).gap (wrap n x.1) (wrap n y.1)):=
      hn.2 (foldUnder n x) (foldUnder n y)
    simpa only [keys,hgap] using edge
  obtain ⟨s,C,hs,hC⟩:=word.cover
  have bounded (x):‖V x‖≤C:=(hC.2 x).trans (mul_le_of_le_one_right hC.1
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) (Nat.cast_nonneg _))))
  let art:Packet (Cloth α) r:=fun z=>∑' y,(∏ i,M (z i) (y i))*V y
  have held (z): drawing V M (List.finRange r) z=art z:=by
    rw [expanded (funded row bounded) _ (List.nodup_finRange r)]
    simp only [show (List.finRange r).toFinset=Finset.univ by ext;simp,full,art]
  have shape:IsSym art:=by
    intro π x
    change (∑' y,(∏ i,M (x (π i)) (y i))*V y)=_
    rw [←(Tuple.perm (Cloth α) π).tsum_eq]
    apply tsum_congr;intro y
    change (∏ i,M (x (π i)) (y (π i)))*V (y∘π)=(∏ i,M (x i) (y i))*V y
    rw [sym π y]
    exact congr_arg (fun t=>t*V y) (Equiv.prod_comp π (fun i=>M (x i) (y i)))
  rw [draft,funext held,symmetric_already art shape]
  funext z;rw [climb_cut];rfl

end YM.Integration.WilsonIndependentConditionalHeldDraft
