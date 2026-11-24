import YM.LocalLTE.XPane.Harbor
import YM.LocalLTE.XPane.Pillar
import YM.LocalLTE.XPre.Hill
import YM.LocalLTE.XPre.Trunk
import YM.LocalLTE.Ticket.Taffeta
/-!
# Actual permissions on THE canonical loader. No leases at larger parameters assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Bandage Mallow
open YM.MergeProof YM.LocalLTE.Vinca YM.LocalLTE LocalLTE.Ticket LocalLTE.River LocalLTE.XPre
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
section
open Push.Local LocalLTE.Dilation Extra.Histories.Doors
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{P:Bolt A}{R:Factor A}
local notation "H"=> Issue.trail P
variable {C:ℕ→ℝ}{W:Bid.Worth}{l:ℕ} (U:Harmonics R C W P l)
-- window opportunities using after-L supports. 
variable {N n m:ℕ} (hm:m<N)
local notation "T"=> U.port N m n hm
local notation "J"=> A.B.a.clock.J (m+1)
local notation "I"=> A.B.a.clock.J m
local notation "Y"=> A.B.a.clock.hatBeta m
set_option quotPrecheck false
open Pressure ConnectedActivityE6 Push.AbsoluteSums
variable (hG:G.Simple)
-- recall after.App durations
open Spiral
variable {M p0 r q TT :ℕ}{κ ζ ε:ℝ}(hr: Spiral.Series R.shape M κ q l r p0 TT ε A.delay)
variable (hκ:∀ N m n:ℕ,∀ hm:m<N, (U.port N m n hm).ac=M ∧ (U.port N m n hm).ranch.allocation.κ=κ)
variable (hp:East.stagnate q 500<l)(hR:∀ i j,(R.target i j).halo=500)
include hr
variable (d j:ℕ)(hd:d+3 ≤ A.B.a.clock.J m)
local notation "jx"=> N-(m+1)
local notation "a"=> Harmonics.inputF hr J I jx
local notation "f'"=> Harmonics.outputF hr J I jx
local notation "u"=> Harmonics.artF hr J I jx
local notation "R1"=> (H).rep N n (m+1)
local notation "S₀"=> (H).rep N n m
local notation "B"=> A.B.a.budget m
local notation "B'"=> (localSection G d)
local notation "F0"=> ((Labels.frames G).level d)
local notation "V'"=> Bandage.aperture U.tag N m n T d hd
local notation "L"=> D.L J
local notation "K₀"=> U.space N m n hm
local notation "Zs"=> (R.shape.μ J I)
local notation "X'"=> X.p.profile I
local notation "Z'"=> X.p.profile J
local notation "κz"=> (T).ranch.allocation.κ
local notation "B0"=> 2* Legato.ticR G (X.p.profile J)
local notation "gn"=> Local.factor (hol G) B' (B).supportExponent (Cub.title G (X.p.profile I))
-- prices minted after Pt.E. Use post-block polynomial.
open LocalLTE.XPre
local notation "VZ"=> U.kube N (m+1) n hm
local notation "e0"=> U.lays d N n m hm
local notation "κg"=> Push.Local.factor (hol G) (localSection G d) ((X.p.profile I).supportExponent) (Cub.title G (X.p.profile I))
local notation "AΓ"=> (sill (X.p.profile I).supportExponent l)
local notation "GS"=> (X.p.profile I).supportExponent
-- ticket-derived appointments.P.Port. localNote:p=scout.
include hκ hG hd
variable (P₀: Extra.Histories.Music ((Labels.frames G).level d) (Issue.trail P) N n)
local notation "ρ0"=> P₀.tone (m+1)
local notation "ρ1"=> P₀.tone m
local notation "P!"=> payG G X' Z' l d L
local notation "X1"=> A.B.a.clock.hatBeta (m+1)
local notation "iT"=> grantZ p0 TT jx
local notation "y"=> X1^(iT)
local notation "β"=> Real.sqrt (A.B.a.clock.forcedAllowance (m+1))
local notation "fT"=> (P!).beam+2*(X1+y+β*(y+y))
local notation "gT"=> (P!).grant+(P!).canopy*((A.B.a.params (m+1)).columns+β*(y+y))
local notation "hT"=>2*(y+β*(y+y))
local notation "age" =>((R1).p)
local notation "tax" => rotationP F0 ((R1).p.order) ((R1).p.power)
open Motion
local notation "total"=> (fun v=> orbitCost F0*(F0).coeffSize ((ρ0).index v))
local notation "D'"=> U.deed N n m hm
local notation "Γi"=> (((H).S.block m).val:ℂ)^d
open MergeProof
variable (X0: ((Labels.frames G).level d).Coeff→ Coefficient ((Labels.frames G).level d) ((Issue.trail P).S.side (m+1) n)) (hz: ShellAt hr d P₀ (m+1) X0) (hb: Heard (localSection G d) (Issue.trail P) N n (hol G) (m+1) (P₀.tone (m+1)))(hh: Chorus (Issue.trail P) N n (m+1) (P₀.tone (m+1)))
variable {Jv:Type}[DecidableEq Jv][Fintype Jv] (Z:Marker.Census Jv)
variable (v:Jv→ ((Labels.frames G).level d).Coeff) {e:ℝ} {pL K:ℕ}
-- Input probes normalization.Birth witness only Quilt.Mark. conditional record.Ag actual.F ignores if unsupported.Sp.Coord.
-- iT jx forced zero.
variable (h' : N=m+1) (hP:Legato.Pinned (X:=X) R.shape κ A.delay M K l pL p0 TT e)
-- Require price at input CURRENT, real e pol due applied separately.
variable (he:∀ i, ((Labels.frames G).level d).coeffSize ((P₀.tone (m+1)).index (v i)) ≤1)
local notation "vv" i=> ((P₀.tone (m+1)).plays (v i))
local notation "vu" i=> ((P₀.tone m).plays (v i))
local notation "pu"=> (fun i=> ((P₀.tone (m+1)|>.plays (v i))).exponentialEntry 0 (localSection G d) (R1)) -- notation `(i)` mandatory
local notation "ku"=> fun i=> profile (R1).activities ((P₀.tone (m+1)|>.plays (v i)).forced)
local notation "z"=> (Γi)⁻¹
local notation "ko"=> fun i=> profile (S₀).activities (z • ((P₀.tone m|>.plays (v i)).forced))
local notation "y1"=> (A.B.a.clock.hatBeta (m+1))
local notation "q1"=> (burnT G d Z' l (D.L J) X' y1 y)
local notation "f1"=> (shapeT G d Z' l (D.L J) X' y)
local notation "s1"=> (rateT G d Z' y)
include hz hb hh he h' hP
open MergeProof
omit [DecidableEq Jv] [Fintype Jv] hP in
lemma amberPX (hu:Arranged H N n (hol G) m (ρ0) (ρ1) (e0) (VZ)) (x:Jv): let z':= (ρ0).index (v x)
    let Vw := U.deed N n m hm
    ∃ Y': Set Lotus.Wing,Y'.Finite ∧ XPre.Circuit Y' Vw d κ a (((D.L J).val)*radiusB Y) 0 0 1 (pu x) (ku x) (ko x) (z' 0) q1 f1 s1:=by
     intro zv Vw; have htop:= step_paid A.B.a m; have hz': jx=0:=by rw [h']; omega
     let g:= (y1); have huX: g=betaF G Y (D.L J):= beta_eq A.B.valid m
     have hj:1 ≤ g:= (A.B.a.fits.delayed _).le; let rWX:= y; let p:= grantZ p0 TT (jx)
     have h0:0 ≤ rWX:=Real.rpow_nonneg (zero_le_one.trans hj) _
     let t:= Γi; let k:ℝ:= (D.L J).val
     have heq:1≤ ‖t‖:=by unfold t; simp_rw [norm_pow, Complex.norm_natCast]; exact one_le_pow₀ (by exact_mod_cast ((Issue.trail P).S.block m|>.property))
     let i:=z
     obtain ⟨L',ht,hY⟩:= U.vacantPX hm hG hr hκ d hd P₀ X0 hz hb hh hu (v x) -- hr shadow `r` param.l.A
     have hv: t*i=1:= mul_inv_cancel₀ (fun he=> by simp only [he,norm_zero] at heq; linarith only [heq])
     have h := XPre.corpo_transport hY 1 i hv.symm
     simp only [norm_one, one_mul,one_smul] at h
     let A':= (P!); let f'':=(R1).p; let s:= Motion.orbitCost (F0)
     have hA:0≤ s:=zero_le_one.trans (Motion.orbitCost_one_le (F0))
     have ht':0≤ total (v x):= mul_nonneg hA (Work.G08.size_nonneg ..)
     have hV1 : total (v x) ≤ s:=mul_le_of_le_one_right hA (he x)
     have hh : ((H).rep N n (m+1)).p=A.B.a.budget (m+1):= P.choice.represents _ _ _ hm|>.vac -- syntax
     have hp: tax=rotationP F0 (Z').order (Z').power:=by rw [hh,Rain.jersey (A:=A) (m:=m+1)|>.1,Rain.jersey (A:=A) (m:=m+1)|>.2.1]
     let κ':=β; have hκ':=Graces.glyphBound A.B.a (m+1); have hz0:0 ≤ tax:= zero_le_one.trans (rotation_one ..)
     refine ⟨_,ht, ?_⟩; change XPre.Circuit _ _ _ _ _ _ _ _ _ _ _ (profile (S₀).activities _) _ _ _ _;rw [profile_scale]; refine XPre.widened h (?_) (?_) le_rfl (?_) -- order: lament prop.I spin
     · let t0:= A'.beam+2*(g+rWX+(rWX+rWX)); have he:0 ≤ t0:= add_nonneg A'.future (mul_nonneg zero_le_two (add_nonneg (add_nonneg (zero_le_one.trans hj) h0) (add_nonneg h0 h0)))
       unfold Legato.burnT; rw [← hp]; exact le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_of_le_one_left (add_nonneg h0 h0) hκ'.2)) zero_le_two)) hz0) ht') (mul_le_mul_of_nonneg_right hV1 (mul_nonneg hz0 he))
     · have hy: ((A.B.a.params (m+1)).columns)=(Z').columns:=by rw [params_eq A.B.valid]
       rw [hy]; let uG:= A'.grant + A'.canopy*((Z').columns+(rWX+rWX)); have hx0 : 0≤ (uG):= add_nonneg A'.pole (mul_nonneg A'.crown (add_nonneg (zero_le_one.trans (Z').columns_ge) (add_nonneg h0 h0)))
       have h : ‖i‖≤1:=by unfold i; rw [norm_inv]; exact inv_le_one_of_one_le₀ heq -- name
       apply le_trans _ (mul_le_of_le_one_left (show 0≤ s*uG from mul_nonneg hA hx0) h); apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
       exact (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_of_le_one_left (add_nonneg h0 h0) hκ'.2)) A'.crown)) ht').trans (mul_le_mul_of_nonneg_right hV1 hx0)
     unfold rateT; rw [←hp]; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_of_le_one_left (add_nonneg h0 h0) hκ'.2)) zero_le_two) hz0) ht').trans (mul_le_mul_of_nonneg_right hV1 (mul_nonneg hz0 (mul_nonneg zero_le_two (add_nonneg h0 (add_nonneg h0 h0)))))
end
end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
