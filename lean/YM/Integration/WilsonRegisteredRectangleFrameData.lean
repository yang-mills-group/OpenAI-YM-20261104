import YM.Integration.WilsonRegisteredRectangleFrameWindow

/-! Dependence of both the weight and the selected prediction on the same actual local Wilson link data. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonRegisteredRectangleFrameData
open Lattice RG RG.Patch Wilson Function Finset
open WilsonRegisteredRectangleTags
open scoped Classical
variable {G:Gauge}

structure Chart (P:Patch)(U V:CoverConfig G):Prop where
  path (x y:P.Points)(k:Lattice.Order):travel U x.val (route x.val y.val k)=travel V x.val (route x.val y.val k)
  bond (x:P.Points)(j:Axis):U (x.val,j)=V (x.val,j)
  face (x:P.Points)(j:PlaqAxes):faceValue U (x.val,j)=faceValue V (x.val,j)

theorem frame {P:Patch}{K:KernelChoices}(legal:P.Branches K G){U V:CoverConfig G}
    (chart:Chart P U V)(a b:P.FrameTag)(tags:a=b ∨ P.usesMin K U):
    P.frame K U a=P.frame K V b ∧ P.frameMass K U a=P.frameMass K V b:=by
  have axial (j:P.FrameTag):P.axial U j=P.axial V j:=funext fun x=>chart.path j.1 x j.2
  have via (h:P.Frame G):P.via h U=P.via h V:=by
    funext x y k;simp only [Patch.via,chart.path]
  have score:P.score U=P.score V:=by funext h;simp only [Patch.score,via]
  have quiet:P.usesMin K U ↔ P.usesMin K V:=by simp only [Patch.usesMin,axial,via]
  by_cases h:P.usesMin K U
  · have ok:P.minimizing V (P.selected U):=by
      simp only [Patch.minimizing,←score];exact (P.min_exists U).choose_spec
    have chosen: P.selected U=P.selected V:=(legal.frame_unique V (quiet.mp h)).unique ok (P.min_exists V).choose_spec
    simp only [Patch.frame,Patch.frameMass,if_pos h,if_pos (quiet.mp h),chosen,and_self]
  have hn:¬P.usesMin K V:=fun q=>h (quiet.mpr q)
  obtain rfl:=tags.resolve_right h
  have faces:P.facesum U=P.facesum V:=by simp only [Patch.facesum,chart.face]
  have cost:P.axialCost U=P.axialCost V:=by funext t;simp only [Patch.axialCost,axial,chart.bond]
  have eligible:P.eligible K U=P.eligible K V:=by simp only [Patch.eligible,cost,faces]
  simp only [Patch.frame,Patch.frameMass,if_neg h,if_neg hn,axial,eligible,and_self]

variable {c f:Side}(S:StepData c f)
abbrev SiteData (U V:Config G f)(o:Site c):Prop:=Chart S.patch (expandAt (S.ratio.embed o) U) (expandAt (S.ratio.embed o) V)
abbrev quiet (U:Config G f)(o:Site c):Prop:=S.patch.usesMin S.kernel (expandAt (S.ratio.embed o) U)

structure BondData (U V:Config G f)(e:Edge (Site c)):Prop where
  source:SiteData S U V e.1
  target:SiteData S U V (e.1+step e.2)
  path (x:S.patch.Points):
    travel (expandAt (S.ratio.embed e.1) U) x.val (List.replicate S.patch.L.val (posDir e.2))=
    travel (expandAt (S.ratio.embed e.1) V) x.val (List.replicate S.patch.L.val (posDir e.2))

theorem site_part (legal:S.patch.Branches S.kernel G){U V:Config G f}(a b:S.SitesChoice)(x:Site c)
    (localData:SiteData S U V x)(tag:a x=b x ∨ quiet S U x):
    site S U a x=site S V b x:=(frame legal localData _ _ tag).2

theorem bond_part (legal:S.patch.Branches S.kernel G)(β:ℝ)(W:Config G c){U V:Config G f}(a b:S.SitesChoice)(e:Edge (Site c))
    (localData:BondData S U V e)(left:a e.1=b e.1 ∨ quiet S U e.1)
    (right:a (e.1+step e.2)=b (e.1+step e.2) ∨ quiet S U (e.1+step e.2)):
    edge S β U W a e=edge S β V W b e:=by
  have l:= (frame legal localData.source _ _ left).1
  have h:= (frame legal localData.target _ _ right).1
  have same:S.connector U a e=S.connector V b e:=by
    funext x;simp only [StepData.connector,StepData.frames,l,h,localData.path]
  funext b;simp only [WilsonRegisteredRectangleTags.edge,same]

end YM.Integration.WilsonRegisteredRectangleFrameData
