import YM.Integration.WilsonIndependentMatchedOwnHomeFiledAxes

/-! On the horizon-four field frame the unit label at an arbitrary test
address is a genuine gauge-constant Wilson insertion on every finite board.
The original blocked spring retains the exact sum over the addressed child
tests, including the engineering weight at horizon four. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedFourUnitCourse
open WilsonCoeffUV WilsonCoeffUV.RootLaw
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Supply Ticket Polestar Shard Plan Mer
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{D k:ℕ}{F:Frame G 4}{T:SectionData F}{p:4<D}{H:Hol G}

def held (n:Side)(v:ℝ):PChart G n:=uband (PowerSeries.C v)

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

private theorem fixed (n:Side)(S:Cost)(x:Site n):
    (fun j r=>revolve x (uband S (U:=Woods G n) j r))=uband S:=by
  funext j
  simp_rw [retail₁]
  exact tilt_zero ..

private theorem joint {a b:Type*}[Fintype a](x:ℝ)(Y:a→ℝ):
    (x • ∑ i:a,uband (U:=b) (PowerSeries.C (Y i)))=uband (C (x * ∑ i:a,Y i)):=by
  funext e r
  by_cases h:r=0
  · subst r
    funext j
    simp_rw [Pi.smul_apply,Finset.sum_apply,uband,shine_lit]
    cases e <;> simp
  rw [uband,shine_dark (Ne.symm h)]
  simp_rw [Pi.smul_apply,Finset.sum_apply,uband,shine_dark (Ne.symm h)]
  simp

theorem block (n:Side)(P:Patch)(KS:KernelChoices)(Q:FaceRow)
    (R:(n:Side)→Matrix (Body 1 (n*P.L)) (Body 1 n) ℝ)(Ñ:ChartRatio G)(X:Scroll D)(k:Cost)
    (Y:PChart G (n*P.L))(T:Vell G (n*P.L) D)(Z:Scroll D→ℝ)
    (paid:∀U:Scroll D,jot (page D U) T=held (n*P.L) (Z U)):
    jot (page D X) (Blue.mix k (collarT P KS Ñ Q R 4 D Y T))=
      held n (tiara P 4 * ∑w:Site P.L,Z (growWord P w D X)):=by
  let V:=page D X
  have h w:jot V (bellOne P KS Ñ Q R 4 D (n:=n) w Y T)=uband (C (Z (growWord P w D X))):=by
    let A:=gatherT P w (wrap (n*P.L) (lift w)) T
    let S:=stepAt P KS n
    let F':=xree P KS n
    have ht:jot (page D X) A=uband (C (Z (growWord P w D X))):=by
      unfold A
      rw [sampledRoot,paid]
      exact fixed ..
    have hh:jot V (reed S F' Q (R n) Ñ Y 4 A)=reed S F' Q (R n) Ñ Y 4 (jot V A):=
      reed_maps S F' Q (R n) 4 (((ContinuousLinearMap.apply ℝ ℝ) V).toLinearMap)
    apply hh.trans
    rw [show jot V A=_ from ht,rumble]
  rw [rootArgument]
  change Blue.mix k (jot V (tiara P 4 • ∑i:Site P.L,bellOne P KS Ñ Q R 4 D i Y T))=_
  rw [map_smul,map_sum]
  simp_rw [h,joint,reset_zinc,reel_C]
  rfl

def returned (A:Levels G)(i:Alma F)(m l:ℕ)(X:Scroll D):ℝ:=match l with
  | 0=>crease X (knurl (notar F i)) 0
  | l+1=>tiara (ll A m) 4 * ∑w:Site (ll A m).L,returned A i (m+1) l (growWord _ w D X)

theorem original (i:Alma F)(literal:Cosmos.sheet F i=0)(A:Levels G)(Ñ:ChartRatio G)(v:T.Sound H)
    (t:Bid.pop T)(N m l:ℕ)(X:Scroll D)(n:Side):
    jot (page _ X) ((walkY A Ñ N m l (starting T p)).1 n i)=held n (returned A i m l X):=by
  induction l generalizing m n X with
  | zero=>exact seed i literal X v t n
  | succ l ih=>rw [walkY];exact block _ _ _ _ _ Ñ X _ _ _ (returned A i (m+1) l) (fun X=>ih (m+1) X _)

theorem null_constant (A:Levels G)(i:Alma F)(pos:0<rankS (notar F i))(m l:ℕ)(X:Scroll D)(c:ℝ)(constant:X.val=fun _=>c):
    returned A i m l X=0:=by
  induction l generalizing m X with
  | zero=>
    dsimp only [returned,crease]
    rw [constant,iteratedFDeriv_const_of_ne (Nat.ne_of_gt pos)]
    simp
  | succ l ih=>
    rw [returned]
    have carried (w:Site (ll A m).L):(growWord (ll A m) w D X).val=fun _=>c:=by
      funext x
      change X.val _=c
      rw [constant]
    simp_rw [ih (m+1) _ (carried _)]
    simp

end YM.Integration.WilsonIndependentMatchedFourUnitCourse
end
