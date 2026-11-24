import YM.RG11Proof.Scale.Portable

/-! # Reverse conversion of the independently specified CS data

Through N with the same β anchoring restrictions; for `Sees` transfer
to the target only need weights powers 0 & 1 of the match. At n=0,
require order-one match in addition or separate `Sees` premise for B.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Scale
open scoped BigOperators Classical Topology
open PowerSeries YM.RG11.Jets YM.PertExtension.Position

variable {K J P : Type*}[Field K][Fintype J]{width:P→ℕ}
variable {L:Constraints K J}{A B:ArrayAt J K width}

private theorem value_head {p:Change K J}(h:nearId p.Z)(hp:Anchored p.g)(v : Mark J width):
    constantCoeff (p.act A v)=constantCoeff (A v):=by
  rw [Change.act, insert_constant]; simp only [base_compose _ _ hp]
  rw [show (fun i j=>constantCoeff (p.Z i j))=(fun i j=> piece 0 p.Z i j) from funext fun _=>funext fun _=>coeff_zero_eq_constantCoeff_apply ..|>.symm,h]
  exact insert_one ..

-- Sees yields no coupling part when β tangent vanish, but need >1 for residual argument.
 theorem mark_to_mark {p:Change K J}(h:Change.Good L p)(hm:∀ v,Through 1 (p.act A v) (B v)) (he:Sees L A): Sees L B:=by
   let q:=Change.one K J
   let C:=piece 1 p.Z
   have Hm (v) : tangent (B v)=orbit (fun z=>constantCoeff (A z)) v C + tangent (A v)* tangent p.g:=by
      have h1: Strike 1 q.g p.g (tangent p.g-1):=by
        unfold q Change.one tangent
        exact ⟨fun i hi=>by obtain rfl: i=0:= Nat.eq_zero_of_le_zero (by omega); rw [coeff_zero_eq_constantCoeff_apply,coeff_zero_eq_constantCoeff_apply,h.ruler.base,constantCoeff_X],by simp [coeff_X]⟩
      have h2 i j: Strike 1 (q.Z i j) (p.Z i j) (C i j):=by
        constructor
        · intro k hk; obtain rfl:k=0:=Nat.eq_zero_of_le_zero (by omega)
          exact congrArg (fun z:Square J K=>z i j) ((Change.Good.id L).field.baseline.trans h.field.baseline.symm)
        unfold q Change.one; by_cases H:i=j <;> simp [Matrix.one_apply,H,C,coeff_one]
      have H: coeff 1 (q.act A v)+(orbit (fun t=>constantCoeff (A t)) v C + tangent (A v)*(tangent p.g-1))=tangent (B v):=
        (pencil_action (n:=1) (A:=A) (p:=q) (q:=p) (by omega) Anchored.variableX nearId_one h1 h2 v).value.trans (hm v 1 le_rfl)
      unfold q at H; rw [Change.act_one, show coeff 1 (A v)=tangent (A v) from rfl] at H
      rw [← H]; ring
   apply LinearMap.ker_eq_bot.mp; apply LinearMap.ker_eq_bot'.mpr
   intro x hx
   let z:Step L:=(⟨x.1.val+x.2 • C,L.vary.add_mem x.1.property (L.vary.smul_mem _ (h.field.positive one_pos))⟩, x.2 * tangent p.g)
   have Hv(v): pencil A v (z.1.val,z.2)=fullRead L B x v:=by
     have hr (v:Mark J width):constantCoeff (B v) = constantCoeff (A v):=(hm v).head.symm.trans (value_head h.field.baseline h.ruler.base _)
     change orbitL _ _ (x.1.val+x.2 • C)+tangent _*(x.2*_) = orbitL _ _ x.1.val + tangent (B v)*x.2
     rw [map_add,map_smul, Hm v, funext hr, smul_eq_mul]
     change orbitL _ _ x.1.val + x.2* orbit (fun t=>constantCoeff (A t)) v C + _ = _
     ring
   have ht : z=0:= he (by rw [map_zero]; exact funext fun v=> (Hv v).trans (congrFun hx v))
   have Hx:x.2=0:=(mul_eq_zero.mp (congrArg Prod.snd ht)).resolve_right h.ruler.nonsingular.ne_zero
   have hw:= congrArg (fun z:Step L=>z.1.val) ht; change x.1.val+x.2 • _=0 at hw; rw [Hx,zero_smul,add_zero] at hw
   exact Prod.ext (Subtype.ext hw) Hx

variable {D:Constraints ℝ J}{p:Change ℝ J}
 theorem both {w:J→ℕ}(h:Change.Good D p){A B:ArrayAt J ℝ width}
     {N:ℕ}(h1:1≤N)(hm:∀v,Through N (p.act A v) (B v))(hx:Sees D A)
     (hX:∀ k≤N,graded w (piece k p.Z))(E:Keeper width)
     {β μ : PowerSeries ℝ}{b m:Square J (PowerSeries ℝ)}(ha:Stem N E w A μ m)(hb:Stem N E w B β b)
     (hβ:Anchored β)(hμ:Anchored μ)(hM:vertical (L:=D) m)(hB:vertical (L:=D) b):
     let q:=p.undo h
     ((∀ k≤N,graded w (piece k q.Z)) ∧ Through N (μ*derivative ℝ q.g) (PowerSeries.subst q.g β) ∧
        MatThrough N (μ • (flash q.Z)) (m*q.Z-q.Z * subs q.g b)) ∧
     Through N (β*derivative ℝ p.g) (PowerSeries.subst p.g μ) ∧
        MatThrough N (β • (flash p.Z)) (b*p.Z-p.Z * subs p.g m):=by
   dsimp only
   have hT:=graded_thru p h.field h.ruler.base hX E hx hm ha hb hβ hM hB
   refine ⟨?_,hT⟩
   let q:= p.undo h
   have he:=clip_agrees N p
   let x:=clip N p
   have hh:Change.Good D x:=⟨⟨he.ruler.head.trans h.ruler.base, (show tangent p.g=tangent x.g from he.ruler.symm 1 h1) ▸ h.ruler.nonsingular⟩,clip_law N p h.field⟩
   have hy:graded w x.Z:=graded.piece_all.mpr fun i=>by
     change graded w (piece i (clip N p).Z); rw [clip_square]; split
     · exact hX _ (by omega)
     · exact graded.zero
   let y:=x.undo hh
   have hu:graded w y.Z:=graded.Law_inv (graded.Law_subs hy hh.field.baseline (reverse_good _ hh.ruler).base) (hh.field.baseline.subs (reverse_good _ hh.ruler).base)
   have hi:MatThrough N q.Z y.Z:= (Change.undo_equiv p x h hh he.symm).field
   have hs(k)(hk:k≤N):graded w (piece k q.Z):=by rw [hi.piece_eq hk]; exact graded.piece_all (A:=y.Z) (w:=w) |>.mp (@hu) k
   exact ⟨hs,graded_thru q (Change.Good.undoes _ h).field (Change.Good.undoes _ h).ruler.base hs E (mark_to_mark h (fun v=> Through.of_le h1 (hm v)) hx)
          (fun _=>(Change.match_reverse p h hm _).symm) hb ha hμ hB hM⟩
end YM.RG11.Scale
