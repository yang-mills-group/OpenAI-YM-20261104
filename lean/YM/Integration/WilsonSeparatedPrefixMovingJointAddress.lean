import YM.Integration.WilsonSeparatedPrefixMovingExteriorTranslation

/-! Move the entire actual far field at an occupied near site into a common physical chart. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJointAddress
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonCoeffUV.Layout
open WilsonIndependentFittedExteriorProfile (home)
open WilsonIndependentMatchedCoverProfile (word)
variable {G:Gauge}{D:ℕ}


def displacement (ε y v:ℝ)(s:Cover)(z o:CellR):Point4:=ε • actualW s+y • z.val-v • o.val
def print (F:Rarity D)(ε y v:ℝ)(s:Cover)(z o:CellR):Rarity D:=
  home F 1 one_pos (displacement ε y v s z o)
theorem ratio (ε x v:ℝ)(hx:x≠0)(s:Cover)(z o:CellR):
    displacement ε ε (ε*v/x) s z o=(ε/x) • Mer.address x v o s z.val:=by
  funext d
  change ε*actualW s d+ε*z.val d-(ε*v/x)*o.val d=(ε/x)*(x*actualW s d-v*o.val d+x*z.val d)
  field_simp;ring
theorem wheel (F:Rarity D)(ε y v:ℝ)(s b:Cover)(z o:CellR):
    wheelC ε y b F.ψ z=wheelC ε v (s+b) (print F ε y v s z o).ψ o:=by
  apply congr_arg (page D)
  apply Subtype.ext
  funext a
  change F.ψ.val (Mer.address ε y z b a)=
    (1:ℝ)⁻¹^4*F.ψ.val (Mer.address (1:ℝ)⁻¹ 0 zeroC 0
      (-(displacement ε y v s z o)+Mer.address ε v o (s+b) a))
  rw [towards0]
  simp only [inv_one,one_pow,one_mul,one_smul]
  apply congr_arg F.ψ.val
  unfold Mer.address Mer.position displacement
  rw [actual_plus]
  module
theorem visits (F:Rarity D)(ε y v:ℝ)(hx:0<ε)(s:Cover)(z o:CellR):
    (VisitsT F ε y z).image (s+·)=VisitsT (print F ε y v s z o) ε v o:=by
  classical
  ext b
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨a,ha,rfl⟩
    rw [visiting hx,←wheel]
    exact (visiting hx).mp ha
  · intro hb
    refine ⟨-s+b,?_,by abel⟩
    rw [visiting hx,wheel F ε y v s (-s+b) z o,show s+(-s+b)=b by abel]
    exact (visiting hx).mp hb
def move (s:Cover):Era G ℝ→ₗ[ℝ]Era G ℝ where
  toFun:=fun V=>shifted V s
  map_add':=by intros;rfl
  map_smul':=by intros;rfl
theorem site (P:TowerS G D)(F:Rarity D)(ε y v:ℝ)(s b:Cover)(z o:CellR):
    move s (locale z (shoe P F ε y b))=locale o (shoe P (print F ε y v s z o) ε v (s+b)):=by
  apply Prod.ext
  · funext per i r w
    change revolve (wrap per s) (revolve (wrap per b) (fun a=>P.1 per i r a (wheelC ε y b F.ψ z))) w=
      revolve (wrap per (s+b)) (fun a=>P.1 per i r a (wheelC ε v (s+b) (print F ε y v s z o).ψ o)) w
    rw [map_add,rollCup,wheel]
  · funext i r w
    change revolve s (revolve b (fun a=>P.2 i r a (wheelC ε y b F.ψ z))) w=
      revolve (s+b) (fun a=>P.2 i r a (wheelC ε v (s+b) (print F ε y v s z o).ψ o)) w
    rw [rollCup,wheel]
theorem original (P:TowerS G D)(F:Rarity D)(ε y v:ℝ)(hx:0<ε)(s:Cover)(z o:CellR)(h:ℕ):
    move s (word P F ε y z h)=word P (print F ε y v s z o) ε v o h:=by
  classical
  rw [word,word,pupil_eye _ _ _ _ _ _ hx,pupil_eye _ _ _ _ _ _ hx,←visits F ε y v hx s z o,
    Finset.sum_image (fun a _ b _=>add_left_cancel),map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [map_smul,site]
theorem appointed (Q:SealR G)(A:Levels G)(C:ChartRatio G)(F:Rarity Q.D)(t b N:ℕ)(y v:ℝ)(s:Cover)
    (z o:CellR)(X:Q.Rider):
    move s (locale z (Q.spins A C F t b N y X))=
      locale o (Q.spins A C (print F (paceT A.S t b) y v s z o) t b N v X):=by
  exact original _ F _ y v (pace_pos ..) s z o Q.h
end YM.Integration.WilsonSeparatedPrefixMovingJointAddress
