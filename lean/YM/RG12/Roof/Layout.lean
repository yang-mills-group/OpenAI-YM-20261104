import YM.RG12.Roof.Echelons
import YM.RG12.Arche.Moor
import YM.Pert.Rigid.Spin
import YM.Next.MAXWELL.System
/-!
# Compatible physical jaws & polarized scale coupling. No Wick identification assumed on C.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Roof
open Function Set Finset Lattice RG Source Maxwell Spec Ward Analysis RG12.Arche Shapes Extra.FD OPE
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}(F:Final C f S)
local notation "A!"=> F.sector.derivatives
local notation "T!"=> freeTable C.labels
local notation "E!"=> Free.scheme C.labels
local notation "hE"=> Free.scheme_filters C.labels
variable (Q:Prescription (A!))(hQ:Q.Coherent)(d:ℕ)(i:RG12.Frames.Grade d)(v:Qname (A!) i→ℂ)
open RG12.Desk.Paired Pert.Scale
abbrev cones (F : Final C f S) (j d:ℕ) (h:j≤d) := lane C S F.sector.derivatives j d h F.room.kernel.laws.toSymmetric F.room.kernel.spin F.phase.transport.comparator F.phase.transport.injection
abbrev glint : RG12.Frames.Col (Desk.Sector (A!) d) →ₗ[ℂ] ((T!).Field d) := rigid _ d F.room.kernel.laws.toSymmetric F.room.kernel.spin F.phase.transport.comparator F.phase.transport.injection
lemma listL (i : RG12.Frames.Grade d)(v:Desk.Sector F.sector.derivatives d i) : glint F d (RG12.Frames.put (Desk.Sector (A!) d) i v)= cones F _ _ i.is_le v:= by apply rigid_block
lemma glinted : Function.Bijective (glint F d):=by
   obtain ⟨q,hq⟩ := OPE.Prescription.chosen F.room.kernel.laws.toSymmetric F.phase.transport.injection
   obtain ⟨T,hT⟩:=beam (A!) F.room.kernel.laws.toSymmetric F.room.kernel.spin F.phase.transport.comparator F.phase.transport.injection hq d
   suffices (glint F d)=T.toLinearMap from this ▸ T.bijective -- test
   apply LinearMap.ext; intro w; rw [← RG12.Frames.by_grade (Desk.Sector F.sector.derivatives d) w,map_sum,map_sum]
   apply sum_congr rfl; intro k _; change glint _ _ _=T _; rw [listL,hT]
open RG12.Frames
lemma dim (s:ℝ) (x:Col (Desk.Sector (A!) d)) : glint F d (dilate (V:=Desk.Sector (A!) d) s x)=gear C.labels d s (glint F d x):=by
    let V:=Desk.Sector (A!) d
    let l (i:ℕ):= ((s^i :ℝ):ℂ)
    have hx(i:Frames.Grade d): Frames.put V i (dilate s x i)= l i.val • Frames.put V i (x i):=by
       ext1 j; by_cases h:i=j
       · subst i; simp only [Frames.put,dilation,Pi.smul_apply,Pi.single_eq_same]; rfl
       simp only [Frames.put, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm h),smul_zero]
    nth_rw 1 [← by_grade V (dilate s x)]; conv_rhs=>rw [← by_grade V x];

    rw [map_sum,map_sum,map_sum]; apply sum_congr rfl; intro i _
    rw [hx,map_smul,listL,gauged]; simp [l]

-- independent free honor, with exact dilation on BOTH slots, after compatible rising
lemma respects (ax:Axis)(s:ℝ)(v:(T!).Field d): (T!).adj (table_spin C.labels) d ax (gear C.labels d s v)= gear C.labels d s ((T!).adj (table_spin C.labels) _ ax v):=by
   simp only [Table.adj,LinearMap.comp_apply,Pert.Scale.gear_conj]
   change Pert.Rigid.wear C.labels _ (Signed.mirror ax) _=_
   rw [Pert.Rigid.wear_ride, Pert.Scale.gear_spin]
   change gear C.labels d s _=gear C.labels d s (Pert.Rigid.wear _ d (Signed.mirror ax) _)
   rw [Pert.Rigid.wear_ride]
omit v i
lemma real_exact (ax:Axis)(m s:ℝ) (hs:s≠0)(x y :(T!).Field d): polished C.labels d d ax m s (gear C.labels d s x) (gear C.labels d s y)=polished C.labels d d ax m 1 x y:=by
   unfold polished; rw [pair_at,pair_at,respects,Shapes.scaling]
   let q:= ![x,(T!).adj (table_spin C.labels) d ax y]
   let p₁ : Fin 2→(T!).Tag:= fun i=> ⟨d,gear C.labels d s (q i)⟩; let p₀ : Fin 2→(T!).Tag:= fun i=> ⟨d,q i⟩
   have he:= points_equ (opens ax m 1 zero_lt_one) q hs
   apply Eq.trans (b:=disc p₁ (s • compass ax m 1)) _ (he.trans _)
   all_goals refine congr_arg (fun p=>disc p _) ?_; funext i; fin_cases i<;>rfl

-- Rises are respected even in different slots: exact before drawing any formation tests
private lemma front {L:Register G}(Z:Table L)(i j k:ℕ)(u:Z.Field i)(v:Z.Field j) (x:Points 2)(A:DiffPlan Z)(_hz:Z.Symmetric)(h:A.Inclusions Z)(ht:i≤k)(hx:x∈conf 2):
    paired Z k j x (A.rise ht u) v = paired Z i j x u v:=by
   let w (_:Fin 1):Z.Tag:=⟨j,v⟩
   have he (k:ℕ)(x:Z.Field k): Fin.cons (α:=fun _=>Z.Tag) ⟨k,x⟩ w= ![⟨k,x⟩,⟨j,v⟩]:=by funext i;fin_cases i <;>rfl
   rw [pair_at,pair_at,← he,← he]; exact h.kernels ht u hx w
private lemma rearP {L:Register G}(Z:Table L)(i j k:ℕ)(u:Z.Field i)(v:Z.Field j)(x:Points 2)(A:DiffPlan Z)(hz:Z.Symmetric)(h:A.Inclusions Z)(ht:j≤k)(hx:x∈conf 2):
    paired Z i k x u (A.rise ht v)= paired Z i j x u v:=by
   rw [pair_at,pair_at]
   let w(_ :Fin 2):Z.Tag:=⟨i,u⟩
   have he(n:ℕ)(a:Z.Field n):Function.update (β:=fun _=>Z.Tag) w (1:Fin 2) (⟨n,a⟩:Z.Tag) = ![⟨i,u⟩,⟨n,a⟩] := funext (fun i=>by fin_cases i <;> simp [Function.update,w])
   rw [←he,←he]; exact A.inclusion_slot (T:=Z) h hz ht hx (1:Fin 2) w v
lemma lifts (X:S.RealSpin)(i j:ℕ)(m:ℝ)(N:ℕ)(ax:Axis)(hH:0 < m)(x:S.Field i)(v:S.Field j)(A:DiffPlan S)(hz:S.Symmetric)(h:A.Inclusions S)(hy:A.Orientation X)(hi:i ≤ d)(hj:j ≤ d):
    illumination _ X d d ax N m (A.rise hi x) (A.rise hj v)=illumination _ X i j ax N m x v:=by
   have ha:= opens ax (N:ℝ)⁻¹ m hH
   unfold illumination; simp only [LinearMap.compl₂_apply,Table.adj,LinearMap.comp_apply]
   rw [hy.realInc,hy.mirrorInc,rearP _ d j d _ _ _ A hz h hj ha, front _ i j d x _ _ A hz h hi ha]
lemma lights (i j:ℕ)(m s:ℝ)(ax:Axis)(hH:0 < m)(x:(T!).Field i)(v:(T!).Field j)(hi:i ≤ d)(hj:j ≤ d):
    polished C.labels d d ax s m ((E!).rise hi x) ((E!).rise hj v)=polished C.labels i j ax s m x v:=by
   have ha:= opens ax s m hH
   have hy: (E!).Orientation (Extra.FD.table_spin C.labels):= Free.phase_orientation _ -- compare proofs? Prop
   unfold polished; simp only [Table.adj,LinearMap.comp_apply]
   rw [hy.realInc,hy.mirrorInc,rearP _ d j d _ _ _ (E!) (table_sym _) (hE) hj ha, front _ i j d x _ _ (E!) (table_sym _) (hE) hi ha]
end YM.RG12.Roof
