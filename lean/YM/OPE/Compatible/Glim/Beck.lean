import YM.OPE.Compatible.Glim.Aurora
/-! # stand chosen avoiding one edge force. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
open Weir Score
variable {n:Side}(H:Even n.val)(p:Limb H)
-- minimum path avoids p.
inductive ExitV (H:Even n.val)(p:Limb H) : ℕ→ Node H→Prop
    | zero:ExitV H p 0 (origin H)
    | goes {i q} (e:Limb H × Bool) (h:e.1≠ p)(hs:(Pond H).start e=q)(hs':ExitV H p i ((Pond H).lastV e)):ExitV H p (i+1) q
lemma exitEdge (x:Site n)(b:Axis)(h:pathX H (x,b)≠ p)(t:{y//y=crumb H x})(i:ℕ)(he:ExitV H p i t.val): ExitV H p (i+1) (crumb H (x+step b)):=by
     -- forward from x+step back
     let y:=x+step b; let q:= negDir b; have ht:(q.used y)=(x,b):=by simp[y,q,Step.used,negDir]
     let e:=forward H q y; refine ExitV.goes e (by change pathX H _≠p;rw [ht];exact h) (stairs H ..|>.1) ?_; rw [show (Pond H).lastV e=t.val from (stairs H ..).2.trans ((by simp[y,q]; exact t.property.symm))];exact he
lemma exitOpp (x:Site n)(b:Axis)(h:pathX H (x,b)≠p)(i:ℕ)(he:ExitV H p i (crumb H (x+step b))):ExitV H p (i+1) (crumb H x):= ExitV.goes (forward H (posDir b) x) h (stairs H ..|>.1) (by rw [show (Pond H).lastV _=_ from (stairs H ..).2];exact he)
lemma ferry_gap (k:Kv)(x:edgeV n): separation (decks k x.1) (ferry k x).1 ≤ 1:=by
     unfold ferry Step.used; split
     next h=> let a:=((posDir x.2).rotate (axisK k)); let y:=decks k x.1; change separation y (y-step a.dir) ≤1
              have hh:= Work.E03.sep_step (y-step a.dir) a.dir; rw [sub_add_cancel,separation_comm] at hh;exact hh
     next h=>simp
lemma Vast (x y:edgeV n)(h:pathX H x= pathX H y)(ht:x≠y): y.2=x.2 ∧ n.val/2 ≤ 1+separation x.1 y.1:=by
     let A:=edgesK H; let t:=pathX H x; let i:=A.tick x; let j:=A.tick y; have hp: ferry i t.val=x:=(resettle H x).symm; have hv:ferry j t.val=y:=by unfold t;rw [h];exact (resettle H y).symm
     let k:=j+i; have he:ferry k x=y:=by rw [←hp, ← ferry_plus H,show k+i=j by unfold k; rw [add_assoc,twinned,add_zero],hv];
     have hq:= deck_free k (show k≠0 from fun h=> ht (by rw [h,ferry_0] at he;exact he)) x.1; have hh:= ferry_gap k x; rw [he] at hh; have hz:= separation_triangle (decks k x.1) y.1 x.1; rw [separation_comm y.1 x.1] at hz; refine ⟨(congr_arg Prod.snd he).symm.trans (ferry_axis ..),?_⟩; omega
lemma smoothPath (h:8 ≤ n.val): ∀ i:Node H,∃ j:ℕ,ExitV H p j i:=by
     have hv:NeZero (n.val-1:ℕ):=⟨by omega⟩
     intro i; rw [← show crumb H i.val=i from See.king_here ..]; apply Pert.Orb.site_induct (n:=n) (fun x=>∃ j:ℕ,ExitV H p j (crumb H x)) ?_ (0:Site n) ⟨0,ExitV.zero⟩ i.val
     rintro x b ⟨k,hk⟩
     by_cases he:pathX H (x,b)=p
     · let y:Axis:= if b=0 then 1 else 0; have hy:y≠b:=by
            unfold y; split
            next h=> rw [h];decide
            next h=>exact Ne.symm h
       have hu(w:Site n): pathX H (w,y) ≠ p:=by
            intro h; exact hy (Vast H (x,b) (w,y) (he.trans h.symm) (fun hh=> hy (congr_arg Prod.snd hh).symm)|>.1)
       have hU:pathX H (x+step y,b)≠p :=by
            have hi:step y ≠ (0:Site n):=by
                have hi:Nontrivial (Per n):= ZMod.nontrivial_iff.mpr (by omega)
                intro h; exact (one_ne_zero (α:=Per n)) (by simpa [Lattice.step] using congr_fun h y)
            intro hP; have ht:x≠ x+step y:=by intro h;exact hi (add_left_cancel (h.symm.trans (add_zero _).symm))
            have hq:= (Vast H (x,b) (x+step y,b) (he.trans hP.symm) (fun h=>ht (congr_arg Prod.fst h))).2; simp only at hq; have hh:= Work.E03.sep_step x y; omega
       let z:=x+step b; refine ⟨_, exitOpp H p z y (hu z) (k+2) ?_⟩; rw [show z+step y=x+step y+step b from add_right_comm ..]; exact exitEdge H p (x+step y) b hU ⟨_,rfl⟩ (k+1) (exitEdge H p x y (hu x) ⟨_,rfl⟩ k hk)
     exact ⟨_,exitEdge H p x b he ⟨_,rfl⟩ k hk⟩
lemma PlotExcept (h:8 ≤ n.val): ∃ T:Plot H,T.Leaf p:=by
    let q(x:Node H):=Nat.find (smoothPath H p h x); have he(x: ↥(({origin H}:Set (Node H))ᶜ)):∃ e:Limb H × Bool,e.1 ≠ p ∧ (Pond H).start e=x.val∧ q ((Pond H).lastV e)<q x.val :=by
         obtain ⟨x,hx⟩:=x; dsimp only; generalize hh:q x=j; have hv : ExitV H p j x:=hh ▸ Nat.find_spec (smoothPath H p h x); cases hv with | zero=> exact (hx rfl).elim | goes e hp hT hQ=>exact ⟨e,hp,hT,Nat.lt_succ_of_le (Nat.find_min' (smoothPath H p h _) hQ)⟩
    choose V hV Ht hq using he; let T:Plot H:=⟨V,q,Ht,hq⟩; refine ⟨T,fun hv=>?_⟩; obtain ⟨z,h⟩:=hv;exact hV _ h
end YM.OPE.Variance
