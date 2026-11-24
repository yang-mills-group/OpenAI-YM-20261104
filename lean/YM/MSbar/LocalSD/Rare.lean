import YM.MSbar.LocalSD.Expect
/-!
Flag occurrence stays rare under supplying kernel even spatially-extended volume.
Use this only on specified list of sites / flagged union; union bound. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bulk
open Lattice Wilson RG Filter Function MeasureTheory PhysicalNext.Repeat.Lotus
open Push Finset Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}{R:Rep G f}
variable {a σ C δ Λ w u v y:ℝ}{X:Support f}
variable (h:R.Lawful σ C Λ δ w)(x:Site f)(b:ℕ→ℝ)(hg:∀ i,0≤ b i∧∀ U,‖R.activities.K i U‖≤ b i)
include hg h
def quake (S:StepData c f)(i:ℕ): Fibre S R:= ⟨.gasKey i,R.activities.K i,h.labels.forced.reads i,h.labels.forced.permit i,trivial,b i,(hg i).2,fun k _=> h.labels.forced.sym i k,h.labels.forced.meas i⟩
omit h hg
variable {b}
lemma pressure (S:StepData c f) (h:R.Lawful σ C Λ δ w) {b:ℕ→ℝ}(hg:∀ i,0≤ b i∧∀ U,‖R.activities.K i U‖≤ b i)(i:ℕ)(k:Finset ℕ)(U:Config G f): (quake h b hg S i).bun k U=(if i∈k then R.activities.gasOccurrence R.p k U else 0):=by
   unfold Fibre.bun Activities.gasOccurrence; split
   next=> unfold Fibre.bill; split
          next hf=> change _=(if i∈k then _ else _); have hx:i∈k:=hf; rw [if_pos hx]; exact mul_prod_erase k (fun i=> R.activities.K i U) hx
          next hn=> rw [if_neg (show i∉k from hn)]
   by_cases h:i∈k <;> simp [h]
lemma pressure_sum (S:StepData c f) (h:R.Lawful σ C Λ δ w) {b:ℕ→ℝ}(hg:∀ i,0≤ b i∧∀ U,‖R.activities.K i U‖≤ b i)(x:Site f)(U: Config G f) : HasSum (fun i:{i:ℕ // x∈ seen R i} => (quake h b hg S i.val).cicada U)
      (if x∈ flags R.p.threshold U then R.eval U else 0) := by
   let H:=R.activities;let q k:= H.gasOccurrence R.p k U; have hh: Summable q:=(H.gasSeries h.labels).summable U
   let j:= {i:ℕ // x ∈ seen R i}
   let g(p:j×Finset ℕ):=(quake h b hg S p.1.val).bun p.2 U
   by_cases hb: x∈ flags R.p.threshold U
   · have hy (k : Function.support q): ∃! i:j,i.val∈ k.val:=by
         have ht:q k.val≠0:=k.prop; unfold q Activities.gasOccurrence at ht; split at ht
         swap; · exact (ht rfl).elim
         next hu=>
         obtain ⟨i,hi,hp⟩:=mem_biUnion.mp (hu.2.symm ▸ hb); refine ⟨⟨i,hp⟩,hi,fun j he=>?_⟩
         by_contra hN; refine Finset.disjoint_left.mp (hu.1 he hi (fun h=>hN (Subtype.ext h))) ((H.forced _).inventory_sup ?_) ((H.forced _).inventory_sup hp); exact j.prop
     let f k:= (ExistsUnique.exists (hy k)).choose; let e:= fun k:Function.support q=> (f k,k.val)
     have hv: Injective e:= fun x y h=> Subtype.ext (congr_arg Prod.snd h)
     have hk(k : Function.support q): (f k).val∈ k.val:= (ExistsUnique.exists (hy k)).choose_spec
     have he (p:j×Finset ℕ)(hP:p∉Set.range e):g p=0:=by
        unfold g; rw [pressure]; split
        next ht=>
          by_contra hh; let x':Function.support q:=⟨p.2, hh⟩
          exact hP ⟨x',Prod.ext (ExistsUnique.unique (hy x') (hk x') ht) rfl⟩
        rfl
     have hz(k): g (e k)=q k.val:= (pressure ..).trans (if_pos (hk k)); have hl : HasSum g (∑' k,q k):= (hv.hasSum_iff he).1 ((((hasSum_subtype_iff_of_support_subset (Set.Subset.refl (Function.support q))).2 hh.hasSum)).congr_fun fun i=> hz i)
     have ht: HasSum (fun v => ∑' k,g (v,k)) (∑' k,q k):=hl.prod_fiberwise fun i=> (hl.summable.prod_factor i).hasSum
     rw [if_pos hb]; exact (ht.mul_left _|>.congr_fun (fun i=>rfl))
   rw [if_neg hb]
   have hf(p:j×Finset ℕ): g p=0:=by
      unfold g; rw [pressure]; split
      next hp=>
        unfold Activities.gasOccurrence; split
        next ha=> exact (hb (ha.2 ▸ mem_biUnion.mpr ⟨p.1.val,hp,p.1.prop⟩)).elim
        rfl
      rfl
   change HasSum (fun i:j=> Real.exp _*(∑' k,g (i,k))) 0; simp only [hf,tsum_zero,mul_zero]; exact hasSum_zero
-- actual flag rarity
lemma probability_flag (V:Config G c)(he:Admitted V R S σ C δ Λ w)(hp:Psalm S R v y)(hv:flags v V=∅)(ht:0≤y)(z:Site f): chance S R V {U: Config G f | z∈ flags R.p.threshold U} ≤ y*w := by
    let A:Set (Config G f):={U | z∈ flags R.p.threshold U}; let W:=A.indicator (fun _=> (1:ℝ)); let q:= W*R.eval
    change S.push R.beta q V/S.push R.beta R.eval V ≤ _; rw [div_le_iff₀ he.mass,mul_comm _ (S.push ..)]
    obtain ⟨b,hb,hB⟩:=he.lawful.labels.boundK; let L:= {i:ℕ // z∈ seen R i}; let U(i:L):=quake he.lawful b hb S i.val
    have hz:∀ a, HasSum (fun i:L=> (U i).cicada a) (q a):=by
        intro s; convert! pressure_sum S he.lawful hb z s using 1; unfold q W; simp only [Pi.mul_apply]; by_cases h:z∈ flags R.p.threshold s
        · simp only [Set.indicator_of_mem (show s∈A from h),if_pos h, one_mul]
        simp only [Set.indicator_of_notMem (show s∉A from h),if_neg h, zero_mul]
    have hw := budget_pull (fun i:L=> i.val) Subtype.val_injective (hB z)
    have hD: SumBudget (fun i:L=> R.p.mass (U i).crest (U i).weight) w:=by
       refine (show ((fun i:L=> R.p.mass (U i).crest (U i).weight)) = (fun i:L=> if z∈ (R.activities.forced i.val).support then R.p.mass (R.activities.forced i.val).support (b i.val) else 0) from funext (fun i=> (if_pos ((R.activities.forced i.val).inventory_sup i.prop)).symm)).symm ▸ hw
    exact (le_abs_self _).trans (remit V he.lawful U hp he.kernel hv _ hz hD (fun i=> ⟨_,rfl⟩) ht he.mass.le)
end YM.MSbar.Bulk
