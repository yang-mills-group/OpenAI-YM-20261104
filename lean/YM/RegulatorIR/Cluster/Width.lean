import YM.RegulatorIR.Cluster.Collapse

/-! Distance currency captured by first joins in the heat flow. Cross carried
on the *same marked functional* L¹, at independent prices. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster.Collapsed
open Set Function Budget Budget.Packet Budget.Tuple Budget.Layer Budget.Tariff Metric
open scoped BigOperators Topology ENNReal NNReal Classical
variable {l d:ℝ} {S T:Set Room} {X:Type} {r s u b:ℕ} {c:ℝ≥0∞}
structure Remotely (S T:Set Room)(d:ℝ):Prop where
  awake : S.Nonempty
  overT : T.Nonempty
  hS : IsClosed S
  hT : IsClosed T
  apart : ∀ x∈ S, ∀ y∈ T, d ≤ dist x y

lemma charge_joins (h:Remotely S T d)(hl:0<l)(x:X→Room)(u b:ℕ)(p:Tuple X r)(q:Tuple X s) (i:X):
     ((realm hl u (S∪T)).uses x).width (Fin.append p q) * amount l b d ≤ ((realm hl (u+b) S).uses x).width (Fin.cons i p)* ((realm hl (u+b) T).uses x).width (Fin.cons i q):=by
 let U:=(realm hl u (S∪T)).uses x; let A m:=(realm hl m S).uses x; let B m:=(realm hl m T).uses x
 rw [amount_plus,amount_plus,mul_mul_mul_comm]
 apply mul_le_mul'
 · apply highest _ _ _ x _ _ (one_le_mul (Premium.width_unit ..) (Premium.width_unit ..))
   intro j; induction j using Fin.addCases <;> rename_i j
   · rw [Fin.append_left]
     have hp:= le_trans (U.width_ge (Fin.cons i p) j.succ) (regions hl u S _ (subset_union_left ..) h.awake x _); rw [Fin.cons_succ] at hp
     exact (mul_one _).ge.trans (mul_le_mul' hp (Premium.width_unit ..))
   rw [Fin.append_right]
   have hp:= le_trans (U.width_ge (Fin.cons i q) j.succ) (regions hl u T _ (subset_union_right ..) h.overT x _); rw [Fin.cons_succ] at hp; exact (one_mul _).ge.trans (mul_le_mul' (Premium.width_unit ..) hp)
 have he:=divided (x i) S T h.awake h.overT h.hS h.hT h.apart
 apply (amount_tri he hl b infDist_nonneg infDist_nonneg).trans
 have H := (A b).width_ge (Fin.cons i p) 0; have V := (B b).width_ge (Fin.cons i q) 0; rw [Fin.cons_zero] at H V; exact mul_le_mul' H V
lemma spliced (h:Remotely S T d)(hl:0<l)(x:X→Room)(u b:ℕ)(Z:Packet X (r+1))(Y:Packet X (s+1)):
   markQ ((realm hl u (S∪T)).uses x) (splice Z Y) * amount l b d ≤ markQ ((realm hl (u+b) S).uses x) Z* markQ ((realm hl (u+b) T).uses x) Y:=by
 let Q:=(realm hl u (S∪T)).uses x; let A:= (realm hl (u+b) S).uses x; let B:= (realm hl (u+b) T).uses x
 rw [markQ,← quota_raised, ← quota_perm (Fin.appendEquiv ..)]
 change quota (fun w:Tuple X r×Tuple X s =>splice Z Y (Fin.append w.1 w.2)) _≤_
 simp_rw [splice_at];apply (inside_quota (fun (w:Tuple X r × Tuple X s) i=>lace Z Y w.1 w.2 i) _).trans
 let f : (Tuple X r× Tuple X s) × X → Tuple X (r+1) × Tuple X (s+1):= fun v=> (Fin.cons v.2 v.1.1, Fin.cons v.2 v.1.2)
 have hf : Function.Injective f :=by
    rintro ⟨⟨p,q⟩,v⟩ ⟨⟨i,j⟩,y⟩ he
    have ht:= Prod.mk.inj ((glueEquiv X r).injective (show glueEquiv X r (v,p)=glueEquiv X r (y,i) from congr_arg Prod.fst he))
    have hh:= Prod.mk.inj ((glueEquiv X s).injective (show glueEquiv X s (v,q)=glueEquiv X s (y,j) from congr_arg Prod.snd he))
    rw [ht.1, ht.2,hh.2]
 let w₀ (z:Tuple X (r+1)×Tuple X (s+1)):= (‖Z z.1‖ₑ*A.width z.1)*(‖Y z.2‖ₑ*B.width z.2)
 unfold quota
 rw [← ENNReal.tsum_prod]; apply le_trans _ ((ENNReal.tsum_comp_le_tsum_of_injective hf w₀).trans_eq ?_)
 · apply ENNReal.tsum_le_tsum; rintro ⟨⟨p,q⟩,i⟩
   change ‖lace Z Y p q i‖ₑ*_≤_; rw [lace,enorm_mul]; exact (mul_le_mul_right (charge_joins h hl x u b p q i) _).trans_eq (mul_mul_mul_comm ..)
 rw [ENNReal.tsum_prod']; simp_rw [w₀, ENNReal.tsum_mul_left,ENNReal.tsum_mul_right]; rfl
lemma away (h:Remotely S T d)(hl:0<l)(x:X→Room)(Z:Packet X (r+1))(Y:Packet X (s+1)){K:Layer X X}(hh:row (swap K) (native _ hl (u+b)) x x c):
   markQ ((realm hl u (S∪T)).uses x) (knot K Z Y) * amount l b d ≤ markQ ((realm hl (u+b) S).uses x) Z* (markQ ((realm hl (u+b) T).uses x) Y*c):=
 (spliced h hl x u b Z (ray 0 Y K)).trans (mul_le_mul_right (ray_mark 0 Y (A:=(fare hl (u+b) T).uses x) (row_mono (A:=(native l hl (u+b)).uses x) (fun a b=>lip hl _ T (x a) (x b)) hh)) _)
end YM.RegulatorIR.Cluster.Collapsed
