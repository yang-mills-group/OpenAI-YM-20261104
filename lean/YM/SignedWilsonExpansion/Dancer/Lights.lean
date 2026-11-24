import YM.SignedWilsonExpansion.Dancer.Fort
/-! # Surjective gathering by Gram. every cap limit identity incl higher rank tie by own filing, map on cluster unipotent.
We prove triangular isometry at largest cap d before all through-cap filings.
-/
set_option autoImplicit false
set_option maxHeartbeats 360000
noncomputable section
namespace YM.SignedWilsonExpansion.Dancer
open XSpace XSpace.Structure1 Normalize Future Gauge Filter Function Matrix
open WilsonCoeffUV.Mer.Xa MarqueQ Stair SeatsW Commission.Gram Shell
open FVA2 FVA2.Dframe Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Menus MS.Land MS.Local.Physical Fort
open scoped BigOperators Topology Classical
variable {G:Gauge}{b d h t w n:ℕ}{ι:Type}{l:Filter ι}
namespace Lights
-- pattern K := captured numerical maps from §25+. Need stochastic.T.
abbrev Sabre (d h:ℕ)(G:Gauge):= ∀ t:ℕ, Sec G t→ₗ[ℂ] Sec G h
abbrev Rise (p:d≤h) : Sec G d→ₗ[ℂ]Sec G h:= Normalize.up p
abbrev distill (t:ℕ)(T:Sabre d h G): FieldEnd G t:= PorchK.prune t h ∘ₗ T t
-- Sabre d/h: d phantom actual caps allowed >d but never queried. family may at other caps be arbitrary
abbrev fee (l:Filter ι)(z:ι→Sabre d h G)(X:Sabre d h G) : Prop:= ∀ t,0<t→t≤d→∀ x:Sec G t, By ℂ l (fun i=> z i t x) (X t x) -- >0 only
structure Horizon (a:Axis)(l:Filter ι)(T:ι→ Point G h 2)(N:ι→Sabre d h G): Prop extends Emblem a l T where
     pos:0<d
     space:d≤h
     orbit_bound (t:ℕ) : 0<t→ t≤d→ ∀ x:Sec G t, By ℂ l (fun i=> N i t ( mirrorB a x) - mirrorB a (N i t x)) 0
     mix {t w:ℕ} (p:0<t) (u:t≤d)(b:0<w)(v:w≤d)(x:Sec G t)(y:Sec G w) : Tendsto (fun i=> Paar (T i) (N i t x) (N i w y)) l (𝓝 (Paar (GramW G h a) (Rise (p:=u.trans space) x) (Rise (p:=v.trans space) y)))
     hewn (t:ℕ):∀ (p:0<t)(u:t≤d)(x:Sec G t), By ℂ l (fun i=> Rise (u.trans space) (distill t (N i) x)- N i t x) 0
structure Gleam (F: Labels.Frames G)(l:Filter ι)(N:ι→Sabre d h G): Prop where
     unitE (p:ℕ):0<p→p≤d→ By ℂ l (fun i=>N i p (leaf G p)) (leaf G h) -- later exact eventual
     credit (t:ℕ):0<t→ t≤d →∀ (j:Toon G t)(k:(F.level t).Index),j.size=t→wt (F.level t) k=t→j.grade≤wr (F.level t) k→
          Tendsto (fun i=>sonar (F.level t) k (distill t (N i) (Logo G t j))) l (𝓝 (sonar (F.level t) k (Logo G t j)))
-- need annotate distill d explicitly if unused
variable {a:Axis} {T:ι→Point G h 2}{N:ι→Sabre d h G}{X:Sabre d h G}
variable (W : Horizon a l T N) (F:Labels.Frames G)(P:Gleam F l N)
include W
protected lemma Horizon.play {V:Filter ι}(t:V≤l): Horizon a V T N :=
     {emblemY W.toEmblem t with pos:=W.pos, space:=W.space, orbit_bound:=fun d p q x=> monoY (W.orbit_bound d p q x) t, mix:=fun p q w r x y=> (W.mix p q w r x y).mono_left t, hewn:=fun d p q x=> monoY (W.hewn d p q x) t }
omit W
include P
protected lemma Gleam.play {V:Filter ι}(t:V≤l): Gleam F V N:=⟨fun d p w=> monoY (P.unitE d p w) t, fun d p q t' i h u v=>(P.credit d p q t' i h u v).mono_left t⟩
omit P
include W
lemma delivers (U:Ultrafilter ι) (hi:(U:Filter ι)≤ l): ∃ X:Sabre d h G, fee (U:Filter _) N X:=by
     have he t (v:0<t ∧ t≤d):∃ x:Sec G t→ₗ[ℂ] Sec G h, ∀ z, By ℂ (U:Filter _) (fun i=> N i t z) (x z):=by
        let B:=Logo G t; let Q:=Logo G h; choose y hy using (fun z: Toon G t=> (by
           let H:= W.toEmblem; let k:=B z; obtain ⟨C,c⟩:= ordinate H (W.orbit_bound _ v.1 v.2 k) ( W.mix v.1 v.2 v.1 v.2 k (mirrorB a k)) Q; exact regroup U Q (fun i=>N i t k) C (c.filter_mono hi) : ∃ x:Sec G h, By ℂ (U:Filter _) (fun i=>N i t (B z)) x ))
        let M:= B.constr ℂ y; refine ⟨M,fixed B fun z=> ?_⟩; rw [Module.Basis.constr_basis]; exact hy z
     let H(t): Sec G t→ₗ[ℂ] Sec G h:= if p:0<t∧t≤d then (he t p).choose else 0; refine ⟨H,fun t v p z=>?_⟩; unfold H; rw[dif_pos ⟨v,p⟩]; exact (he t ⟨v,p⟩).choose_spec z
variable [l.NeBot]
variable (qF:fee l N X)
include qF
lemma working {t:ℕ}(p:0<t)(q:t≤d)(x:Sec G t) : X t x= Rise (q.trans W.space) (distill t X x) := by
    have hp:= addY (W.hewn _ p q x) (qF t p q x); rw [zero_add] at hp; apply SeatsW.solitary (viaY hp (Eventually.of_forall (fun i=> sub_add_cancel .. ))) (translateBy ((Rise (q.trans W.space)).comp (PorchK.prune (G:=G) t h)) (qF _ p q x)); -- underscore elaborate
lemma moves {t w:ℕ}(p:0<t)(u:t≤d)(v:0<w)(y:w≤d)(x:Sec G t)(b:Sec G w):
     Paar (GramW G h a) (X t x) (X w b)= Paar (GramW G h a) (Rise (u.trans W.space) x) (Rise (y.trans W.space) b):=
     tendsto_nhds_unique (p_emit W.toEmblem (qF _ p u x) (qF _ v y b)) ( W.mix p u v y x b )
lemma glossy (p:0<t)(q:t≤d)(x:Sec G t) : X t (mirrorB a x)=mirrorB a (X t x):=by
     have ht:= mirror_dual a (qF _ p q x); refine solitary (qF _ p q _) (viaY (x:=mirrorB a (X t x)) (by simpa only[zero_add] using addY (W.orbit_bound _ p q x) ht ) (Eventually.of_forall fun i=> sub_add_cancel .. ))
def record (x y:Sec G h)(a:Axis):= Paar (GramW G h a) x (mirrorB a y)
def recoR (x y:Sec G d)(a:Axis):= record x y a -- redundant
lemma movesS {t w:ℕ}(p:0<t)(u:t≤d)(v:0<w)(y:w≤d)(x:Sec G t)(b:Sec G w):
     record (X t x) (X w b) a= recoR (Rise (u.trans W.space) x) (Rise (y.trans W.space) b) a:=by
     unfold record recoR; rw [← glossy W qF v y]; exact moves W qF p u v y _ _
section
omit W qF [l.NeBot]
lemma fallsA (x y z:Sec G h) : record (x-y) z a= record x z a-record y z a:=map_sub (acts (GramW G h a) (mirrorB a z)) x y
lemma fallsB (x y z:Sec G h) : record x (y-z) a= record x y a-record x z a:=by
     unfold record; simp_rw [mirror_sub,actors,map_sub, LinearMap.sub_apply]
lemma risingR (x y:Sec G d)(p:d≤h): record (Rise p x) (Rise p y) a= record x y a := by
     unfold record; let z:= GramW G d a; let M:= GramW G h a; change Paar M _ (Rise p (mirrorB a y))=_; unfold Paar; unfold M GramW; rw [screen,screen]; exact congr_arg _ (funext fun i=> by fin_cases i <;> rfl)
end
lemma coherentT (p:0<t)(u:t≤d)(v:t≤w)(s:w≤d)(x:Sec G t): X w (Rise v x)= X t x:=by
    let X':= X w (Rise v x); let Y:= X t x; have hp:=lt_of_lt_of_le p v; let K:= Rise (u.trans W.space) x; let z:= record K K a; apply sub_eq_zero.mp; apply onPeak (a:=a); change record (X'-Y) (X'-Y) a=0; rw [fallsA,fallsB,fallsB]; rw [show record X' X' a=z from movesS W qF hp s hp s _ _,show record Y X' a=z from movesS W qF p u hp s _ _,show record X' Y a=z from movesS W qF hp s p u _ _,show record Y Y a=z from movesS W qF p u p u _ _]; abel
lemma crossLimit (x y:Sec G d): record (distill d X x) (distill d X y) a = record x y a:=by
    let p:= W.mix W.pos le_rfl W.pos le_rfl x y; have ht:= movesS W qF W.pos le_rfl W.pos le_rfl x y; rw [working W qF W.pos le_rfl x,working W qF W.pos le_rfl y,risingR] at ht; exact ht.trans (risingR x y W.space)
lemma nests (u:t≤d)(p:0<t)(z:Sec G t) : distill d X (Rise u z)= Rise u (distill t X z):=by
    apply ( Submodule.inclusion_injective ( Maxwell.Free.chain (G:=G) W.space )); let y:= Rise u z; change Rise W.space (distill d X y)=Rise (u.trans W.space) _; rw [← working W qF W.pos le_rfl y, ← working W qF p u z, coherentT W qF p u u le_rfl z]; -- Maxwell.chain namespace
include P
lemma settles (p:0<t)(u:t≤d)(i:Toon G t)(w:i.size=t)(j:(F.level t).Index)(ht:wt (F.level t) j=t)(hp: i.grade ≤ wr (F.level t) j):
     sonar (F.level t) j (distill t X (Logo G t i)-Logo G t i)=0:=by
     let Z:=sonar (F.level t) j; rw [map_sub,sub_eq_zero]; exact tendsto_nhds_unique (translateBy ( PorchK.prune t h) (qF _ p u (Logo G t i)) Z) (P.credit t p u i j w ht hp) -- h
lemma settled (p:0<t)(u:t≤d)(i:Toon G d)(w:i.size=t)(j:(F.level d).Index)(ht:i.size≤ wt (F.level d) j)(hp:i.size=wt (F.level d) j → i.grade≤wr (F.level d) j):
     sonar (F.level d) j (distill d X (Logo G d i)- Logo G d i)=0:=by
     subst t; let φ:= distill d X; let x:= Logo G i.size (seated i); let Y:=distill i.size X x-x
     rw [film i,nests W qF u p, ←map_sub]; by_cases v:i.size=wt (F.level d) j; · let y:=downL F u j v.symm.le; rw [← up_down F u j v.symm.le]; rw [ breathe_up _ u y]; exact settles W F P qF p u (seated i) rfl y ((congr_arg Prod.fst (down_grade F u j v.symm.le)).trans v.symm) ((hp v).trans (congr_arg Prod.snd (down_grade F u j v.symm.le)).symm.le)
     exact nearer j u (Rise u Y) (lt_of_le_of_ne ht v) Y.property
lemma respects {t:ℕ}(i j:Toon G d)(p:t=i.size)(hv:0<t)(u:t≤ j.size)(v:t=j.size→ i.grade ≤ j.grade):
    (Logo G d).coord j (distill d X ( Logo G d i )-Logo G d i)=0:=by
    subst t; apply Fort.drop j (F.level d); intro t ht; have hw:wt (F.level d) t=j.size:=congr_arg Prod.fst ht; exact settled W F P qF hv (size_le i) i rfl t (u.trans_eq hw.symm) (fun h=>(v (h.trans hw)).trans_eq (congr_arg Prod.snd ht).symm)
-- unipotency proved by lower-rank fixed guarantee
lemma dream (k:ℕ)(i:Toon G d) (hP:i.size * (d+1)+ i.grade=k) : distill d X (Logo G d i)= Logo G d i := by
   induction k using Nat.strong_induction_on generalizing i with | h k ih=>
   let e(j:Toon G d):= Logo G d j; let A:= distill d X; by_cases h':i.size=0
   · obtain ⟨u,U⟩:= zero_orig i h'
     have h₁:= P.unitE d W.pos le_rfl; have ht: X d (leaf G d)= leaf G h:=SeatsW.solitary (qF d W.pos le_rfl _) h₁
     rw [U,map_smul]; congr 1; rw [distill,LinearMap.comp_apply,ht]; exact PorchK.pruned_up (leaf G d) W.space
   let x:= A (e i)-e i
   have hp:A x=x:=by
      rw [← (Logo G d).sum_repr x,map_sum]; refine Finset.sum_congr rfl fun j _=>?_
      rw [map_smul]; by_cases u:j.size < i.size
      · have he:j.grade < d+1:= Nat.lt_succ_of_le (Glyph.memory j); have hK : (j.size+1)*(d+1) ≤ i.size * (d+1):= Nat.mul_le_mul_right _ u; rw [add_mul, one_mul] at hK; exact congr_arg _ (ih (j.size*(d+1)+j.grade) (by omega) j rfl)
      by_cases v:j.size=i.size ∧ j.grade < i.grade
      · exact congr_arg _ (ih (i.size*(d+1)+j.grade) (by omega) j (by rw [v.1]))
      rw [show (Logo G d).repr x j=0 from respects W F P qF i j rfl (Nat.pos_of_ne_zero h') (le_of_not_gt u) (fun e=> not_lt.mp fun p=> v ⟨e.symm,p⟩),zero_smul,zero_smul]
   have hz:= crossLimit W qF (e i) x; rw [show distill d X x=x from hp] at hz; apply sub_eq_zero.mp; apply onPeak a; exact (fallsA ..).trans (sub_eq_zero.mpr hz) -- `fallsA` orientation test
omit qF
section
omit [l.NeBot]
lemma identityLimits (p:0<t)(u:t≤d)(z:Sec G t) : By ℂ l (fun i=> N i t z) (Rise (u.trans W.space) z):=by
    apply regularX; intro U hu; let K := (U:Filter ι)
    obtain ⟨x,h⟩:= delivers W _ hu
    let Q:= W.play hu; let B:= Logo G d; have hX: distill d x=(1:Module.End ℂ (Sec G d)):= B.ext (fun i=>dream Q F (P.play F hu) h _ _ rfl)
    let y:= Rise u z; have hz:x t z= Rise (u.trans Q.space) z:=by rw[← coherentT Q h p u u le_rfl z,working Q h W.pos le_rfl y, hX]; rfl
    rw [← hz]; exact h _ p u z
end
end Lights
end YM.SignedWilsonExpansion.Dancer
