import YM.Integration.WilsonPositionProgramTrialPublicJointSourceParityCash
import YM.Integration.WilsonIndependentMatchedFourUnitProjection

/-! A unit gauge insertion on its actual inherited prior remains scalar for every test through all admitted upper ages. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointScalarCourse
open WilsonCoeffUV WilsonCoeffUV.RootLaw
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Supply Ticket Polestar Shard Plan Mer
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{D k h:ℕ}{F:Frame G h}{T:SectionData F}{p:h<D}{H:Hol G}

open WilsonIndependentMatchedFourUnitCourse (held block)
theorem seed (i:Alma F)(literal:Cosmos.sheet F i=0)(X:Scroll D)(v:T.Sound H)(t:Bid.pop T)(n:Side):
    jot (page _ X) ((starting T p).1 n i)=held n (crease X (knurl (notar F i)) 0):=by
  have val:valence F i=0:=by rw [valence,literal,F.zero_degree]
  have row:=birthFormula T p v t n X i
  dsimp only at row
  apply by_flash (k:=valence F i) (l:=0)
  · exact jot_length _ (herald_norm T p i n)
  · exact uband_length _ _ 0
  · exact fun j=>jot_code _ (herald_auth T p i n j)
  · exact fun j=>uband_cost _ _ j
  unfold held
  rw [uband_flash]
  rw [literal,val,pow_zero,one_mul,show (fun Y:Lawn (Woods G n)=> (T.places (Pi.single 0 1) 0 (mantle Y)).re)=
    (fun _=>(1:ℝ)) from funext fun _=>congr_arg Complex.re (congr_fun v.unit _),jet_const,map_one] at row
  rw [row,Algebra.smul_def,mul_one,real_alg,soil,map_C]
  rfl

theorem scalar (n:Side)(c t:ℝ):c • held (G:=G) n t=held n (c*t):=by
  funext e r
  by_cases yes:r=0
  · subst r
    funext x
    simp_rw [Pi.smul_apply,held,uband,shine_lit]
    cases e <;> simp
  funext x
  simp [Pi.smul_apply,held,uband,shine_dark (Ne.symm yes)]

def Given (P:TowerS G D)(Z:Scroll D→ℝ):Prop:=∀n X,jot (page D X) (P.1 n)=held n (Z X)

theorem step (A:Levels G)(O':ChartRatio G)(simple:G.Simple)(valid:LocalRatio O')
    (N m h k:ℕ)(now:m<N)(four:4≤k)(P:TowerS G D)(zero:On 0 P)
    (Z:Scroll D→ℝ)(offer:Given P Z):
    ∃Y:Scroll D→ℝ,Given (Spout A O' N m h k P) Y:=by
  let Q:=ll A m
  refine ⟨fun X=>gradeH Q h 4 * (tiara Q 4*∑w:Site Q.L,Z (growWord Q w D X)),?_⟩
  intro n X
  rw [←saturate A O' (h:=h) now simple valid zero (by decide : 0≤4) four]
  change jot (page D X) (gradeH Q h 4 • cloakP A O' N m 4 n (P.1 (n*Q.L)))=_
  rw [map_smul]
  unfold cloakP
  rw [block n Q _ _ _ O' X _ _ _ Z (offer _)]
  exact scalar ..

theorem traveled (A:Levels G)(O':ChartRatio G)(simple:G.Simple)(valid:LocalRatio O')
    (N h k m j:ℕ)(before:m+j≤N)(four:4≤k)(P:TowerS G D)(zero:On 0 P)
    (Z:Scroll D→ℝ)(offer:Given P Z):
    ∃Y:Scroll D→ℝ,Given (spools A O' N k h m j P) Y:=by
  induction j generalizing P Z with
  | zero=>exact ⟨Z,offer⟩
  | succ j ih=>
    have now:m+j<N:=by omega
    obtain ⟨Y,t⟩:=step A O' simple valid N (m+j) h k now four P zero Z offer
    exact ih (by omega) _ (ShedG A O' now simple valid zero (Nat.zero_le _)) Y t

theorem original (A:Levels G)(O':ChartRatio G)(simple:G.Simple)(valid:LocalRatio O')
    (N k m j:ℕ)(before:m+j≤N)(four:4≤k)(T:SectionData F)(fit:h<D)
    (sound:T.Sound H)(pop:Bid.pop T)(a:Alma F)(lit:Cosmos.sheet F a=0):
    ∃Y:Scroll D→ℝ,Given (spools A O' N k h m j (vein (starting T fit) a)) Y:=by
  have rank:valence F a=0:=by rw [valence,lit,F.zero_degree]
  exact traveled A O' simple valid N h k m j before four _ (hailed _ (freshly T H fit sound pop) a rank.le)
    _ (fun n X=>seed a lit X sound pop n)

end YM.Integration.WilsonPositionProgramTrialPublicJointScalarCourse
