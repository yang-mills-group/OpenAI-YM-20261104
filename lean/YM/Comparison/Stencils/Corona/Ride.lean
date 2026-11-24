import YM.Comparison.Stencils.Corona.Epoch
/-!
# Cover Wick automorphism on V field only, all orientations

`blaze` leading input primary data for the *actual* `T`.
No stability costs inferred from triangular basis. Import
`Vertex`'s parity and complex conventions unchanged and check projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Stencils.Corona
open Filter Set Function Finset Lattice MvPolynomial Symbols Source Source.Drops Labels
open Next.Foundations Next.Rank Next.Rank.Normal PertExtension
open scoped BigOperators Topology ContDiff Classical Matrix.Norms.Frobenius
variable {G: Gauge} {d : ℕ}
lemma trail_rot (H:Hol G)(s:Signed) (d:ℕ) (J:Jet G) :
   access (trunk d (Motion.rotJ s J)) = tour s 0 (access (trunk d J)):=by
 funext i
 let X:=trunk d J; let Y:=trunk d (Motion.rotJ s J)
 let a:= (posDir i.2).rotate s; let z:= affine s 0 i.1
 let b (t:ℝ):=G.mat (H.links d (expand d (t • Y)) 1 i)
 let w (t:ℝ):=H.links d (expand d (t • X)) 1
 have he t:b t=G.mat (a.read (w t) z):=by
   have ht(t:ℝ): expand d (t • Y)=Motion.rotJ s (expand d (t • X)) := by
        funext i; by_cases hu:i<d-1 <;> simp [expand,Motion.rotJ,X,Y,Labels.changedJet,hu,Drops.trunk]
   unfold b; rw [ht,Motion.rotJ,← Work.G01.swirls_of_flow H s]; rfl
 have hl : HasDerivAt b (G.colorMat (tour s 0 (access X) i)) 0:=by
   change HasDerivAt _ (G.colorMat (if a.neg then -access X (a.used z) else access X (a.used z))) _
   have h:= (Work.G02.linkGerm H d (a.used z)).2.2 X
   rw [funext he]; split <;> rename_i ht
   · unfold Step.read; simp_rw [if_pos ht,G.mat_inv]; rw [map_neg,← G.colorMat_skew]; exact h.star
   unfold Step.read; simp only [ht]; exact h
 have hp : HasDerivAt b (G.colorMat (access Y i)) 0:= (Work.G02.linkGerm H d i).2.2 Y
 have ht:=hp.unique hl
 exact G.colorMat_injective ht
lemma scrolls (H:Hol G) (s:Signed) (p q:Primary G)
   (h:∀ A, demonstrates (tour s 0 A) p=demonstrates A q):
   rotated s.ortho (scape G d p)= scape G d q:=by
  rw [printed,printed]; apply Feed.sole_poly _ _ d (moved_limit (d:=d) (cap_limited ..) _) (cap_limited ..)
  intro J k hk
  change iteratedDeriv k (fun t=>Labels.read (scaleJet J t) (rotated s.ortho (Heat.Ray.clipped d p))) 0 = iteratedDeriv k (fun t=>Labels.read (scaleJet J t) (Heat.Ray.clipped d q)) 0
  simp_rw [Motion.rotated_reads, show ∀ t:ℝ,Motion.rotJ s (scaleJet J t)=scaleJet (Motion.rotJ s J) t from fun t=>funext fun i => map_smul _ _ _]
  rw [deriv_read,deriv_read,Heat.Ray.clipped,Heat.Ray.clipped,tier_capRead d _ _ hk,tier_capRead d _ _ hk,← deriv_read, ← deriv_read]
  apply Filter.EventuallyEq.iteratedDeriv_eq k
  refine Eventually.of_forall fun x=>?_; simp only [Heat.Ray.display_jet]
  rw [show scaleJet (Motion.rotJ s J) x=Motion.rotJ s (scaleJet J x) from funext fun i => (map_smul ..).symm]
  change demonstrates (access (trunk d _)) p=demonstrates (access (trunk d (scaleJet J x))) q
  rw [trail_rot H]; exact h _

variable {F:Labels.Frame G d}{T:SectionData F}{H:Hol G}

/-- Leading primary data rendered from section. Only need polynomial
representing the operator's restriction to link space; not asserting
`rendered`'s use of slots fits the certified `stencil`. Use `ColumnsUse`
in actual expansion. -/
def blaze (H:Hol G)(T:SectionData F)(h:T.Sound H)(hp:Bid.pop T):F.Coeff→ₗ[ℂ] Primary G:=
  ∑ i:F.Index, (LinearMap.proj i).smulRight ((LatticePT.topMatrix T H h hp).basis i)
lemma blazes (H:Hol G)(T:SectionData F)(h:T.Sound H)(hp:Bid.pop T)(x:F.Coeff):
    blaze H T h hp x=∑ i:F.Index,x i • (LatticePT.topMatrix T H h hp).basis i:=by simp [blaze]
lemma plated (i:F.Index) (h:T.Sound H)(hp:Bid.pop T):
    Binds ((LatticePT.topMatrix T H h hp).basis i) (columnSeries T i 0):=by
  intro A; rw [column_value, ← recorded]
  let D:= (Heat.Top.rendered T hp).toData
  let B:= D.columns i; let p:= D.shape i
  let n:= (F.grades i).2
  have he: PowerSeries.coeff (0+n) (recording fun t:ℝ=> cylinder T i (linksOf (t • A)))=
     PowerSeries.coeff (0+n) (PowerSeries.X ^ n * formsSeries A n B p):=by
    apply congr_arg
    rw [show cylinder T i=Bid.lumin p ∘ Bid.mapped B from Heat.Top.rend_acts h hp i]; exact forms_exact _ _ (D.low i)
  rw [he,PowerSeries.coeff_X_pow_mul, forms_leading A B (D.low i)]; symm
  change demonstrates A (rename _ (portion n p))=_
  rw [demonstrates,aeval_rename]; rfl
lemma title (x:F.Coeff)(h:T.Sound H)(hp:Bid.pop T):
    Binds (blaze H T h hp x) (columns T x 0):=by
 intro A
 rw [Stencils.portion_eval,blazes,map_sum]; simp only [map_smul]
 exact Finset.sum_congr rfl fun i _=> congr_arg _ (plated i h hp A)

def reel (H:Hol G)(T:SectionData F)(h:T.Sound H)(hp:Bid.pop T): F.Coeff≃ₗ[ℂ] F.Coeff:=
   (LatticePT.topMatrix T H h hp).conversion (ambient G)
lemma current_bill (x:F.Coeff)(h:T.Sound H)(hp:Bid.pop T):
    (F.coords.symm (reel H T h hp x)).val=scape G d (icing (blaze H T h hp x)):=by
  classical
  have he : reel H T h hp x=Heat.Top.joint F (icing (blaze H T h hp x)) := by rw [blazes,map_sum,map_sum]; simp only [map_smul]; rfl
  have ht : Hue.Fixed (icing (blaze H T h hp x)):=Hue.Fixed.heat (show Hue.Fixed (blaze H T h hp x) from ?_)
  case refine_1 =>
    intro u A; rw [blazes, map_sum,map_sum]; exact Finset.sum_congr rfl fun i _=>by rw [map_smul,map_smul,LatticePT.Vertex.basis_fixed T H h hp i u A]
  rw [he, printed, Heat.HueTag.shadow_eq _ ht]; rfl
lemma roll (T:SectionData F) (h:T.Sound H)(hp:Bid.pop T) (x:F.Coeff) (p:Primary G)
    (v:Binds p (columns T x 0)) : scape G d (icing p) = (F.coords.symm (reel H T h hp x)).val:=by
 rw [current_bill]
 exact scape_account (icing_iff.mpr (fun A=> (v A).symm.trans (title x h hp A)))
lemma calibrated (T:SectionData F)(h:T.Sound H)(hp:Bid.pop T) (x:F.Coeff) (p:Primary G)
    (v:Binds p (columns T ((reel H T h hp).symm x) 0)):
    scape G d (icing p)=(F.coords.symm x).val:=by rw [roll T h hp _ p v, LinearEquiv.apply_symm_apply]
lemma commutes (T:SectionData F)(h:T.Sound H)(hp:Bid.pop T) (x:F.Coeff) (s:Signed):
    reel H T h hp (F.act s.ortho x)=F.act s.ortho (reel H T h hp x):=by
  apply F.coords.symm.injective; apply Subtype.ext; let M:=reel H T h hp
  rw [current_bill _ h hp];
  let p:=blaze H T h hp x; let q:=blaze H T h hp (F.act s.ortho x)
  rw [show F.coords.symm (F.act s.ortho (M x))=tensor s.ortho (F.coords.symm (M x)) from ?_]
  · change scape G d (icing q)=rotated s.ortho (F.coords.symm (reel H T h hp x)).val; rw [current_bill _ h hp]
    have hh: Accounts (escort s 0 p) q:=by
      intro A; rw [fling]; exact (title x h hp _).symm.trans ((Motion.spins h x s 0 A).trans (title (F.act s.ortho x) h hp A))
    exact Eq.symm (scrolls H s (icing p) (icing q) (fun A=>by rw [← fling,journeys]; exact icing_iff.mpr hh A))
  nth_rw 1 [← F.coords.apply_symm_apply (M x)]; rw [Frame.act_coords, LinearEquiv.symm_apply_apply]
lemma actual_real (x:F.Coeff)(h:T.Sound H)(hp:Bid.pop T):
    reel H T h hp (star x) = star (reel H T h hp x):= LatticePT.Vertex.bar_map T H h hp x
end YM.Comparison.Stencils.Corona
