import YM.OPE.Compatible.Blaze.Mirth
/-! # Climb reflection under trunk subspace -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix Tree
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir Stationary
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell Char FreeResolvent Paver Rill Pilot Prairies Woody Virgin
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
open YM.AnalyticNext.QuarticMatch.Joint
variable {N c f:Side}{G:Gauge}{L:RG.KernelChoices}{P:ChartRatio G}{d k j r w e m:ℕ} {I J:Type} (a:Axis) (g:Ratio c f)(h:Odd g.count.val)
local notation "F"=> forest g h
abbrev dart (s:Site N):= (Wm a).act s
abbrev spur (E:Edge (Site N)):=sendEdge (Wm a) 0 E
include h
lemma baseg (x:Site f): g.parent (dart a x)=dart a (g.parent x) ∧ g.residue (dart a x)=dart a (g.residue x):=by
     obtain ⟨⟨x,y⟩,rfl⟩:=g.assemble_bijective.surjective x; rw [show dart a (g.assemble (x,y))=g.assemble (dart a x,dart a y) from ?_];simp; unfold Ratio.assemble; dsimp only; unfold dart; rw [Signed.act_add,wrap_signed,Ratio.lift_signed_of_odd h]; simp
lemma windH (x:Site f)(he:leaf g x): leaf g (dart a x)∧ (forest g h).up (dart a x)=((forest g h).up x).rotate (Wm a):=by
      rw [leaves g _] at *; simp only[forest,(baseg a g h x).2]; constructor
      · exact fun hh=> he ((Wm a).act_injective (hh.trans (Signed.act_zero ..).symm))
      exact rises _ (fun _=>rfl) h he
omit h in
lemma thru (x:Site f)(i:Step): spur a (i.used x)=(i.rotate (Wm a)).used (dart a x):=by
      rcases i with ⟨i, _ | _⟩
      · unfold spur sendEdge; rw [show ((Step.used _ _).1)=x from rfl]; simp [affine,dart];rfl
      change spur a (x-step i,i)= _; unfold spur; rw [errand]; unfold Step.used; rw [Step.rotate]; rw [Signed.act_sub,show (Wm a).act (step i)= (if i=a then -step i else step i:Site f) from by simpa using norm_step a i (0:Site f)]; by_cases h:i=a <;> simp [Signed.mirror, Wm,h,dust,dart, sub_eq_add_neg,eq_comm (a:=a)]
lemma flank (i:Edge (Site f))(hp:i∈(forest g h).trunks):spur a i∈(forest g h).trunks:=by
      rw [Forest.trunk_mem_iff] at hp ⊢; obtain ⟨x,he,rfl⟩:=hp; obtain ⟨h₁,h₂⟩:=windH a g h _ he; exact ⟨_,h₁, (congrArg (fun p:Step=>p.used _ ) h₂).trans (thru a x ((forest g h).up x)).symm⟩
omit h in
lemma twise (i:Edge (Site N)):spur a (spur a i)=i:=by obtain ⟨x,i⟩:=i; unfold spur; rw [errand,errand,offsets]
local notation "W"=> Forest.Free (forest g h)
def Orbits (i:W):W:=⟨spur a i.val,fun ht=> i.property (by have hv:= flank a g h _ ht; rw [twise] at hv; exact hv)⟩
lemma Ztwice(x:W): Orbits a g h (Orbits a g h x)=x:=Subtype.ext (twise ..)
def atlasW : Equiv.Perm W:= ⟨Orbits a g h,Orbits a g h,Ztwice a g h,Ztwice a g h⟩
local notation "Y"=> AxisChart G (forest g h)
def plank : Y→L[ℝ] Y:= ContinuousLinearMap.pi fun i=> if i.val.2=a then -(ContinuousLinearMap.proj (atlasW a g h i)) else ContinuousLinearMap.proj (atlasW a g h i)
lemma bloom (x:Y)(v:W):plank a g h x v= if v.val.2=a then -x (atlasW a g h v) else x (atlasW a g h v):=by unfold plank; rw [ContinuousLinearMap.pi_apply];split <;>rfl
lemma bloom2 (x:Y):plank a g h (plank a g h x)=x:=by
    ext1 i; rw [bloom]; have hv:(atlasW a g h i).val.2=i.val.2:=by have ht:=congr_arg Prod.snd (errand a i.val.2 i.val.1); exact ht
    simp_rw [bloom,hv,show atlasW a g h (atlasW a g h i)= i from Ztwice ..];split <;> simp
omit h
lemma EPath (T:StepData c f)(h:Odd T.ratio.count.val)(x:AxisChart G (forest T.ratio h)) : fieldF (forest T.ratio h) (plank a T.ratio h x)=Lattice.pull (Wm a) 0 (fieldF (forest T.ratio h) x):=by
     ext1 i; rw [show Lattice.pull (Wm a) 0 (fieldF (forest T.ratio h) x) i=(if i.2=a then (fieldF (forest T.ratio h) x (spur a i))⁻¹ else fieldF (forest T.ratio h) x (spur a i)) from ?_]; swap; · obtain ⟨i,j⟩:=i; rw [η_line,spur,errand]
     by_cases ht:i∈ (forest T.ratio h).trunks
     · rw [show fieldF _ _ _= _ from (show fieldF (forest T.ratio h) (plank a T.ratio h x) i= 1 from (forest T.ratio h).on_tree _ ⟨_,ht⟩), show fieldF _ _ (spur a i)= 1 from (forest T.ratio h).on_tree _ ⟨_,flank _ _ h _ ht⟩];simp
     let p: (forest T.ratio h).Free:=⟨i,ht⟩; let Z:=atlasW a T.ratio h; rw [show fieldF _ _ _=_ from (show fieldF (forest T.ratio h) (plank a T.ratio h x) i= _ from (forest T.ratio h).off_tree _ p),show fieldF _ _ (spur a i)= _ from (show fieldF (forest T.ratio h) x (spur a i)=_ from (forest T.ratio h).off_tree _ (Z p))]; unfold expF; rw [bloom]; change G.lieExp (if i.2=a then -x (Z p) else x (Z p))= _; split_ifs; exact Work.F03.exp_neg_color _; rfl
end YM.OPE.Quit
