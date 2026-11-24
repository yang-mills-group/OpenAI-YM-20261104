import YM.OPE.Compatible.Scrape.Trell
import YM.Extra.WILSON_STARTUP.Curvature
/-!
# Rooted log-link slice of a coherent box -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{E X:Type*}{n:Side}{i k r m:ℕ}
local notation "T"=> Shade G
local notation "A"=> fieldX (Shade G)
section
noncomputable def sprig (p:Cover)(w:Walk):fieldX (Shade G) →ₗ[ℝ] G.Color:={
    toFun x:= (pieces x p w).sum
    map_add' x y := by induction w generalizing p with
                       | nil=>simp only[pieces,List.sum_nil,zero_add]
                       | cons a w ih=> rw [pieces,List.sum_cons,pieces,pieces,List.sum_cons,List.sum_cons,ih]; have hx(e:Edge Cover): indexS e (x+y)=indexS e x+indexS e y:=rfl; split <;> simp_all only <;> abel
    map_smul' v x := by induction w generalizing p with
                        | nil=> rw [pieces,List.sum_nil,pieces,List.sum_nil,smul_zero]
                        | cons a w ih=> rw [pieces,List.sum_cons,pieces,List.sum_cons,ih]; have hp(e:Edge Cover): indexS e (v • x)=v • indexS e x:=rfl; rw [hp]; split <;> simp_all } -- adjust
abbrev Inn (v:fieldX G.ColorIndex)(p:Cover):G.Color:=WithLp.toLp 2 fun i=> v (p,i)
lemma uphill (v:fieldX G.ColorIndex) (p:Edge Cover): indexS p (mountain v)=Inn v (p.1+step p.2)-Inn v p.1:=rfl
lemma sprigUp (p:Cover)(w:Walk)(v:fieldX G.ColorIndex): sprig p w (mountain v)=Inn v (stop p w)-Inn v p:=by
      change (pieces _ _ _).sum=_; induction w generalizing p with
      | nil=> simp [pieces,stop]
      | cons a w ih=> rw [pieces,List.sum_cons,ih,stop,uphill]; rcases a with ⟨i,v|v⟩<;> simp only [Step.used, Step.vec, Bool.false_eq_true, ↓reduceIte, sub_eq_add_neg] <;> abel
abbrev actualAt (p:Edge Cover) :A→ₗ[ℝ] G.Color:=⟨⟨fun i=> indexS p i, fun _ _=>rfl⟩,fun _ _=>rfl⟩ -- mk syntax
noncomputable abbrev royal (p:Edge Cover):fieldX (Shade G) →ₗ[ℝ] G.Color:= actualAt p + sprig 0 (carryP p.1)-sprig 0 (carryP (p.1+step p.2)) -- START p wrong
lemma champ (p:Edge Cover)(x:A): royal p x=indexS p (risingO x):=by
      ext1 i; change x (p.1,p.2,i)+bandC x p.1 i - bandC x (p.1+step p.2) i = x _+(- (bandC x _ i) - (- (bandC x _ i))); abel
lemma sham (p:Edge Cover)(x:fieldX G.ColorIndex): royal p (mountain x)=0:=by
      change indexS p _+sprig _ _ _-sprig _ _ _=_; rw [uphill,sprigUp,sprigUp]; unfold carryP; rw[route_end,route_end]; abel
lemma sprite (p:Cover)(w:Walk)(x:A)(u:G.El): sprig p w (plumeX u x)=G.adjoint u (sprig p w x):=by
      change (pieces _ _ _).sum= G.adjoint _ (pieces _ _ _).sum; induction w generalizing p with
      | nil=> simp [pieces]
      | cons i w ih=>
           have ht : indexS (i.used p) (plumeX u x) = G.adjoint u (indexS _ x):=rfl
           have he : (if i.neg then -(G.adjoint u (indexS (i.used p) x)) else G.adjoint u (indexS (i.used p) x))=G.adjoint u (if i.neg then -indexS (i.used p) x else indexS (i.used p) x):=by split <;> simp
           rw [pieces,List.sum_cons,pieces,List.sum_cons,map_add,ih,ht,he]
lemma ShamRock (p:Edge Cover)(x:A)(u:G.El): royal p (plumeX u x)=G.adjoint u (royal p x):=by
      change indexS p _+sprig _ _ _-sprig _ _ _= G.adjoint u (indexS _ _+ _-_); rw [map_sub,map_add,sprite,sprite]; rfl -- adjust
end
end YM.OPE.Spells
