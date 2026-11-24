import YM.OPE.Measuring.Narrow

/-! Smooth germs of actual readout values in the noncollision slot case.
This is at finite horizon, so moving the outer variables doesn't take any
coefficient-entrance limit. No dependence on perturbative labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Measuring.Tree
open Orbits Orbits.Reader Prescription Nesting Nesting.Tree Function Filter Set Table
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {n:ℕ}{f:Fin n→Tree}{t:Tree}

lemma nice (h:Narrow t){M:ℝ}(hM:0≤M): ∃ M':ℝ,M ≤ M' ∧ ∀ {a:t.Inner→ℝ} {z:t.Plot}, Tapered t 1 1 a → Immediate M 1 t a z → Relative M' 1 t a z:=by
    induction t with
    | bud => exact ⟨M,le_rfl,fun _ _=>trivial⟩
    | fork n f ih=>
       choose F hF ht using fun j=>ih j (under_narrow h j)
       let K:=∑ v:Fin n,F v
       have hk(v): F v ≤ K:=Finset.single_le_sum (f:=F) (fun v _=>hM.trans (hF v)) (Finset.mem_univ v)
       refine ⟨K+M,show M ≤ K+M from le_add_of_nonneg_left (Finset.sum_nonneg fun i _=>hM.trans (hF i)),fun {a} {z} he hj=>?_⟩
       let r := a (Sum.inl ())
       have hr:0<r:=he.positive _
       have hv(j):Relative (F j) 1 (f j) (childAge j a) (childPlace j z):=ht j ((he.2.2 j).mono le_rfl (by change (_:ℝ)*1 ≤ _; rw [mul_one]; exact he.2.1)) (hj.2.2 j)
       refine ⟨?_,fun i j _ _ he=> (he ((branch_sub h).allEq _ _)).elim, fun j=>(hv j).mono (he.2.2 j) ((hk j).trans (le_add_of_nonneg_right hM)) le_rfl⟩
       rintro (⟨⟩|⟨i,w⟩)
       · rw [show z (Sum.inl ()) - z (fork n f).topSeat = 0 from sub_self _,norm_zero]; exact mul_nonneg (add_nonneg (Finset.sum_nonneg fun i _=>hM.trans (hF i)) hM) hr.le
       have hw : ‖childPlace i z w - childPlace i z (f i).topSeat‖ ≤ F i*r := ((hv i).from_current w).trans (by
           obtain ⟨hu',ho⟩:=(he.2.2 i|>.on_boundary (by exact mul_nonneg hr.le zero_le_one)); exact mul_le_mul_of_nonneg_left (ho.trans_eq (mul_one _)) (hM.trans (hF _)))
       exact (c_dist_point (childPlace i z w) (childPlace i z (f i).topSeat) (anchor z)).trans ((add_le_add (hw.trans (mul_le_mul_of_nonneg_right (hk i) hr.le)) (hj.1 i)).trans_eq (add_mul ..).symm)

lemma immediate_of_relative {M η:ℝ}{a:t.Inner→ℝ}{z:t.Plot}(h:Relative M η t a z):Immediate M η t a z :=by induction t with
 | bud=>trivial
 | fork n f ih=>exact ⟨fun i=>h.1 (.inr ⟨i,(f i).topSeat⟩),fun i j hi=>h.2.1 _ _ _ _ hi, fun i=> ih i (h.2.2 i)⟩

abbrev Nonroot {n:ℕ}(f:Fin n→Tree):= Σ i,(f i).Inner
abbrev Rates (n:ℕ) (f:Fin n→Tree):= Sum Unit (Nonroot f)→ℝ

def parametrise (w:Nonroot f→ℕ)(x y:ℝ)(b:Nonroot f→ℝ):Rates n f
 | Sum.inl _=> x
 | Sum.inr v=> y^(w v) * b v

abbrev Fork(f:Fin n→Tree):= Nesting.Tree.fork n f
lemma model_base (z:(Fork f).Plot){r:Nonroot f →ℝ}(b:ℝ): model (fork n f) b (Sum.elim (fun _=>0) r) z=fun _=>b • z (.inl ()):=by
    funext v; rcases v with _|⟨i,v⟩; rfl
    rw [model]; change b • z _ + model (f i) (b*0) _ _ _ = b • z _; rw [mul_zero]; exact add_eq_left.mpr (model_zero (f i) _ _ _)
where model_zero (t:Tree)(r:t.Inner→ℝ)(z:t.Plot)(v:t.Positions):model t 0 r z v=0:=by induction t with
   | bud=>exact zero_smul _ _
   | fork n f ih=> rcases v with _ | ⟨i,v⟩; exact zero_smul ..; rw [model,zero_smul,zero_add,zero_mul,ih i]

lemma parametrise_zero {w:Nonroot f→ℕ}(q)(x y:ℝ) :parametrise w 0 y q=Sum.elim (fun _=>0) (fun i=>y^(w i)*q i):=by funext v; cases v<;>rfl

variable {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]
lemma parametrise_smooth{w:Nonroot f→ℕ}{q:V→Nonroot f→ℝ}{x y:V→ℝ}(hx:ContDiff ℝ ∞ x)(hy:ContDiff ℝ ∞ y)(h:∀i,ContDiff ℝ ∞ (fun k=>q k i)):ContDiff ℝ ∞ (fun t':V=>parametrise w (x t') (y t') (q t')):=by
    refine contDiff_pi.mpr fun j=>?_ ; cases j with
    | inl=> exact hx
    | inr i=> exact (hy.pow _).mul (h _)

def headNat : (t:Tree)→(t.Leaf→ℕ)→ t.Inner→ℕ
 | bud,_,i=>nomatch i
 | fork _ _,a,.inl ⟨⟩=>∑ v,a v
 | fork _ f,a,.inr ⟨i,v⟩=>headNat (f i) (childWages i a) v
lemma head_cast (t:Tree)(a:t.Leaf→ℕ)(j:t.Inner): (headNat t a j:ℝ)=headSum t (fun i=>(a i:ℝ)) j :=by
    induction t with
    | bud=> cases j
    | fork n f ih=>rcases j with ⟨⟩|⟨i,j⟩; rw [headSum,headNat,Nat.cast_sum]; congr 1; exact ih i _ j

def whole(t:Tree)(u:t.Leaf→ℕ)(r:t.Inner→ℝ):ℝ:= ∏ v:t.Inner,(r v)^headNat t u v
lemma whole_good (t:Tree){u r}(hr:∀j:t.Inner,0<r j):0 < whole t u r:= Finset.prod_pos (fun i _=> pow_pos (hr i) _)

lemma whole_offset {u r}(m:ℝ)(hr:∀j:(Fork f).Inner,0<r j): whole (Fork f) u ((Fork f).ratios 1 r) * toll (fun v=>(u v:ℝ)) 0 m r= r (.inl ())^m:=by
      let t:=Fork f; let q:= (fork n f).ratios 1 r; have hq (v:t.Inner) :0<q v:= ratio_pos (show 0< (1:ℝ) from one_pos) hr v
      rw [← toll_eq (w:=fun v=>(u v:ℝ)) (hr ..)]
      unfold whole scaleFee; change _*(r (.inl ())^m * ∏ v,(q v)^(-(t.headSum _ v)-0))=_
      rw [mul_comm, mul_assoc,← Finset.prod_mul_distrib]; simp only [sub_zero]; trans (r (.inl ()))^m * ∏ v, (q v)^(-(headNat t u v:ℝ)) * (q v)^(headNat t u v:ℝ)
      · apply congr_arg (_*·) (Finset.prod_congr rfl fun v _=>by rw [show (Fork f).headSum _ v = (headNat t u v:ℝ) from (head_cast t u v).symm,Real.rpow_natCast]);
      simp_rw [show ∀v,(q v)^(-(headNat t u v:ℝ)) * q v^(headNat t u v:ℝ)=1 from (fun v=>by rw [← Real.rpow_add (hq v),neg_add_cancel,Real.rpow_zero])]; simp
where ratio_pos {t:Tree}{p:ℝ}{r:t.Inner→ℝ}(hp:0<p)(hr:∀j,0<r j)(v:t.Inner):0<t.ratios p r v:=by induction t generalizing p with
  | bud=>cases v
  | fork n f ih=>rcases v with ⟨⟩|⟨i,v⟩; exact div_pos (hr _) hp; exact ih i (hr _) (fun k=>hr _) v

section Fields
variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Extraction.Order}
    (U:Spec.Final C F S) (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (v:(Fork f).Leaf→S.Tag) {m:ℕ}(c:R.channels m)(D:(Fork f).Inner→ℕ)
    (z:(Fork f).Plot)

private lemma coef_sum_inj {a b:R.channels m→ℂ}(h:(∑ i:R.channels m,a i • R.actor m i) = ∑ i,b i • R.actor m i):a=b:=by
    have h': (∑ i,a i • R.basis m i) = ∑ i,b i • R.basis m i:=Subtype.ext (by change (R.stratum m).subtype _ = (R.stratum m).subtype _; simp only [map_sum,map_smul]; exact h)
    exact Eq.trans ((R.basis m).repr_sum_self a).symm ((congr_arg (fun v:R.stratum m=>(fun i=>(R.basis m).repr v i)) h').trans ((R.basis m).repr_sum_self b))

lemma output_carry (a:E4):Kernel.output U R (fun i=> z i+a) v c=Kernel.output U R z v c:= congr_arg ((R.basis m).repr · c) (Subtype.ext (R.fresh_transport ..))
lemma chord_carry (a:E4):Kernel.chord U R (fun i=> z i+a) v c D = Kernel.chord U R z v c D:=congr_fun (coef_sum_inj U R (a:=fun c=>Kernel.chord U R (fun i=>z i+a) v c D) (b:=fun c=>Kernel.chord U R z v c D) (show _ from Motion.stacked_shift U R z (voices v) D m a)) c

private lemma trivial_margin (h:Narrow t) (o:E4)(m:ℕ):orbitMargin R.port m (fun (_:t.Leaf)=>o) o:=by
    intro i hi k e he; apply beside_distinct.mpr ⟨fun _ _ _=>(leaf_sub h).allEq _ _,(beside_distinct.mp (bearing_clear e)).2.1,fun p b hp=>?_⟩; apply (beside_distinct.mp (bearing_clear e)).2.2 () b (by simpa only [sole,away,comp_apply,sub_self] using hp)
private lemma trunk_margin (h:Narrow (Fork f)) (o:E4)(m:ℕ):orbitMargin R.port m (fun (_:Fin n)=>o) o:=by
    intro i hi k e he; apply beside_distinct.mpr ⟨fun _ _ _=>(branch_sub h).allEq .., (beside_distinct.mp (bearing_clear e)).2.1,?_⟩; intro p b hp; exact (beside_distinct.mp (bearing_clear e)).2.2 () b (by simpa only [sole,away,comp_apply,sub_self] using hp)
lemma constant_aperture (h:Narrow t)(p:E4)(m:ℕ){D:t.Inner→ℕ}: (fun _:t.Positions=>p)∈Kernel.aperture U R t m D:=by induction t generalizing m with
 | bud=> trivial
 | fork _ _ ih=>exact ⟨fun s=> trunk_margin U R h p s.val,fun i=> ih i (h.2 i) _⟩
set_option maxHeartbeats 800000 in
lemma smooth_plot (d:Bool) (h:Narrow (Fork f))(p:E4):∀ᶠ x in 𝓝 (fun _:((Fork f)).Positions=>p), ContDiffAt ℝ ∞ (fun x:(Fork f).Plot=>if d then Kernel.output U R x v c - Kernel.chord U R x v c D else Kernel.output U R x v c) x:=by
    let q: (Fork f).Plot := fun _=>p
    have hM: q∈{z:(Fork f).Plot|orbitMargin R.port m (Nesting.Tree.profile z) (anchor z)}:= trivial_margin U R h p m
    have h₀:= (Kernel.collar_open U R m (t:=Fork f)).mem_nhds hM
    have hΓ:q∈Kernel.aperture U R (Fork f) m D:= constant_aperture U R h p m
    have h₁:= (Kernel.stencil U R D m).mem_nhds hΓ
    filter_upwards [h₀, h₁] with y hy hΓ; change orbitMargin R.port m (Nesting.Tree.profile y) (anchor y) at hy
    split_ifs; exact (Kernel.output_smooth U R v c hy).sub (Kernel.chord_smooth U R v c D hΓ); exact Kernel.output_smooth U R v c hy
end Fields
end YM.OPE.Measuring.Tree
