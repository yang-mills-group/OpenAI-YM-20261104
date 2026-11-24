import YM.SchemeRG11.Air.Attic
/-! External estimates supply defect envelope. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Air
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook
open Labels Long MvPolynomial
open scoped Classical Pointwise
variable {G:Gauge}{m n:ℕ}{T:Align.Itinerary}{R r:ℝ}{F U:Falls G}{f g:Ban G}
abbrev Twin(T:Align.Itinerary)(R:ℝ)(m:ℕ)(F A:Falls G):Prop:=∀ (i:G.ColorIndex)(a:Axis)(s:Fliers), Local T R ((m:ℤ)+1) ((m:ℤ)-s.card) (fun j=>fleet s (ribbon F i j a-ribbon A i j a))
lemma skirt (hr:0<r)(x:Cover){g:Slate}{u v:ℤ}(h:Local T r u v g):Wall T (fun _ _=>True) u 0 (fun i _=>g i x):=by obtain ⟨C,hC,H⟩:= hatch_iff.mp (noted h hr x); exact ⟨C,hC,H.mono (fun _ hi _ _=>by rw [zpow_zero,mul_one]; exact hi)⟩
lemma window_leg (k:Bool)(h:r<R)(hp:r>0)(ht:Blue T R F)(hU:∀ i a, ribbon U a i∈team ℝ m)(hc:Twin T R m F U)(a:Touch G)(ha:a∈Stepper G n): Defect T r R (m+1) F U (n+1) (if k then Long.castV (leaf a) else swift a):=by
 induction ha using Submodule.span_induction with
 | mem z e=>
    obtain ⟨i,s,H,rfl⟩:=e; subst n; have he:=ht.shore i.2 i.1.2 s;have hC:=hc i.2 i.1.2 s
    let l:=i.1.1; let f(i':ℕ):=fleet s (ribbon F i.2 i' i.1.2); let g(i':ℕ):=fleet s (ribbon U i.2 i' i.1.2)
    have hz : Local T R ((m:ℤ)+1) ((m:ℤ)-s.card) (f-g):=by
       convert hC using 1; funext j x; simp only [f,g,map_sub,Pi.sub_apply]
    let k':ℤ := s.card
    cases k
    · apply Defect.born
      · simp only [Bool.false_eq_true,↓reduceIte,swift, Haze.realTaste,dip,add_comm _ i.1.1]; change Local T r _ _ (fun i z=> f i (l+z)); convert Long.fold (Wall.moving (guardian T h l) he) (k'+1) (by unfold k'; omega) using 1 <;> dsimp only [k']<;> omega
      · simp only [Bool.false_eq_true,↓reduceIte,swift,Haze.realTaste,dip,add_comm _ i.1.1]; convert Wall.moving (guardian T h l) hz using 1 <;> (first | omega|rfl)
      intro p w t v e; have hj:=ht.came i.2 i.1.2 s _ t _ (e.shift l)
      simp only [Long.swift,Bool.false_eq_true,↓reduceIte,Haze.realTaste,dip]; exact hj -- direction lacking Streams witness
    · have hx(Q:Shaft G→ℝ):aeval Q (leaf (vane0 i s))= fleet s (Long.element Q i.1.2 i.2) l:=by rw [Haze.realTaste,← flex_zero (vane0 i s),dip,zero_add]
      have hn : Local T r ((m:ℤ)+1) ((m:ℤ)-s.card) (fun i z=> f i (l+z)-g i (l+z)):= Wall.moving (guardian T h l) hz
      apply Defect.born
      · simp only [if_true,Long.castV,hx]; convert Long.fold (T:=T) (S:=r) ((skirt (hp.trans h) l he).inherit (W:=Near T r) (Eventually.of_forall (fun _ _ _=>trivial))) (k'+1) (by unfold k'; omega) using 1 <;> first|dsimp only [k']; abel|rfl
      · simp only [if_true,Long.castV,hx]; -- wait s.card>N -> target negative powers. Wall moving above gave origin f(l)-g(l); can't weaken v<0! Need s≥m => high Leg at center estimate stronger h^(s+1) inherits Wall.fold. hC difference at l f/p private? U may AC at high if s≥m, since shape lies in team. require extra hC-high
        rw [show ((m+1:ℕ):ℤ)=m+(1:ℤ) from Nat.cast_add_one m]; by_cases HH:s.card< m
        · apply Wall.weaken (T:=T) ((skirt (hp.trans h) l hz).inherit (W:=Near T r) (Eventually.of_forall fun _ _ _=>trivial)) (by omega)
        have he' (k:ℕ): fleet s (Long.element (U k) i.1.2 i.2) l=0:=congrFun (member.mp (cap_height (le_of_not_gt HH) (team_wing (hU k i.2) i.1.2)) s rfl) l
        simp_rw [he',sub_zero]; convert Long.fold (T:=T) (S:=r) ((skirt (hp.trans h) l he).inherit (W:=Near T r) (Eventually.of_forall (fun _ _ _=>trivial))) (k'-m) (by unfold k'; omega) using 1 <;> first|dsimp only [k']; abel|rfl
      intro p w t v q; simp only [if_true,Long.castV,hx]; exact ht.came i.2 i.1.2 s 0 (by rw [norm_zero]; linarith) _ (World.Along.base l)
 | zero=>
    have hx:(if k then castV (leaf (0:Touch G)) else swift (0:Touch G))=0:=by funext i z; cases k<;>simp [castV,swift]
    rw [hx]; exact Defect.pure_null
 | add a b _ _ fa fb=>
    convert Defect.add fa fb using 1; cases k <;> ext l x m<;> simp [castV,swift]
 | smul c a _ h=>
    convert h.scale c using 1; cases k<;>ext l x m<;> simp [castV,swift]
lemma buoy(c:ℕ→ Sky G n→ℝ)(u:G.ColorIndex)(i:ℕ): ribbon (shapeV T c) u i∈team ℝ n:=by rw [rib]; exact Submodule.sum_mem _ fun b _=> Submodule.smul_mem _ _ (team_height b.fst.isLt (finched b))

def summit (h:r<R)(p:r>0)(ht:Blue T R F)(c:ℕ→ Sky G n→ℝ)(he:Twin T R n F (shapeV T c)):Long.Volume G T where
 classV:= Defect T r R (n+1) F (shapeV T c)
 nest x b hx:=by induction hx with
   | unit=> exact Defect.init1 ..
   | zero=>exact Defect.pure_null
   | add y t q a=> exact q.add a
   | mul y t q a=> exact q.multiply a
   | scale y s a=> exact a.scal s
   | piece a k=> exact window_leg false h p ht (fun i a=> buoy c a i) he a k
 add:= Defect.add
 mul:= Defect.multiply
 coin:= fun x b t w=>w.scale _
 scale:=fun y s=> y.scal s
 anchor a k hx:= window_leg true h p ht (fun i a=>buoy c a i) he a hx 
end YM.SchemeRG11.Air
