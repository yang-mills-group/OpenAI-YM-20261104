import YM.LocalLTE.Sail.Tunes
import YM.LocalLTE.XPane.House
/-!
# A cone of market bounds on the ACTUAL panels
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
open Bandage Mallow Coterie
open YM.MergeProof YM.LocalLTE.Vinca YM.LocalLTE LocalLTE.Ticket LocalLTE.River LocalLTE.Sail
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{P:Bolt A}{R:Factor A}
variable {C:ℕ→ℝ}{W:Bid.Worth}{l:ℕ}(U:Harmonics R C W P l)
local notation "H"=> Issue.trail P
variable {N n d:ℕ} (V:Extra.Histories.Music ((Labels.frames G).level d) (Issue.trail P) N n) (f:((Labels.frames G).level d).Coeff)
    {r0:ℕ}(hv:Sung (localSection G d) (Issue.trail P) N n (hol G) W r0 V)
local notation "T₀"=> localSection G d
set_option quotPrecheck false
local notation "F"=> ((Labels.frames G).level d)
local notation "T"=> A.B.a
local notation "c" i=> (Issue.trail P).S.block i
local notation "σ" i=> Sail.sampleNorm H N d i
local notation "J'" i=> A.B.a.clock.J i
local notation "Z"=> A.B.a.clock
variable {m:ℕ}
local notation "I'"=> J' m
local notation "J"=> J' (m+1)
local notation "x"=> (Z).hatBeta m
local notation "y"=> (Z).hatBeta (m+1)
local notation "b"=> D.L (J)
open Lotus Motion
open Spiral Pressure ConnectedActivityE6
variable {M p0 r q TT :ℕ}{κ ζ ε:ℝ}{AX: Almanac}(hr: Spiral.Chronicles R.shape M κ q l r p0 TT ε A.delay AX)
variable (hκ:∀ N m n:ℕ,∀ hm:m<N, (U.port N m n hm).ac=M ∧ (U.port N m n hm).ranch.allocation.κ=κ)
variable (hG:G.Simple)
variable (he:((Labels.frames G).level d).coeffSize f ≤ 1) -- notation
variable (M':Motion) (o:∀ i,Site ((Issue.trail P).S.side i n))(hm:m<N)(hp:o (m+1)=(A.B.a.clock.op m n).ratio.embed (o m))
variable (h:r0≤ m)(hy:N-m≤TT+1)
local notation "Y"=> betaF G x b
local notation "t'"=> grantZ p0 TT (N-(m+1))
local notation "u"=> Y^t'
local notation "p₁"=> X.p.profile J
local notation "q₀"=> X.p.profile I'
-- post funds, booked by uniform post parameters. input stage covariance.
abbrev chanT (G:Gauge)(d:ℕ)(p:Stage)(l:ℕ)(L0:Side)(q:Stage)(s t a:ℝ):ℝ:=s*(rotationP ((Labels.frames G).level d) p.order p.power*burnT G d p l L0 q t a)
abbrev chanF (G:Gauge)(d:ℕ)(p:Stage)(l:ℕ)(L0:Side)(q:Stage)(s a:ℝ):ℝ:= s*shapeT G d p l L0 q a
abbrev chanK (G:Gauge)(d:ℕ)(p:Stage)(s a:ℝ):ℝ:= s*(rotationP ((Labels.frames G).level d) p.order p.power*rateT G d p a)
local notation "Yx"=> capStone X.p I' TT
local notation "o'"=> hue
local notation "k'"=> AX.demand J I' (N-(m+1))
local notation "L"=> (D.L J).val* Pressure.radiusB x
local notation "U₁"=> V.tone (m+1)
local notation "R₁"=> (Issue.trail P).rep N n (m+1)
variable (hd:d+3 ≤ (Issue.trail P).levels.clock.J m)(hh:Chorus (Issue.trail P) N n (m+1) (V.tone (m+1)))(hA: Vinca.Arranged (Issue.trail P) N n (hol G) m (V.tone (m+1)) (V.tone m) (U.lays d N n m hm) (U.kube N (m+1) n hm))
include hr hv hp hy h hh hG hκ he hd hA
variable (Q: ((Labels.frames G).level d).Coeff→ Coefficient ((Labels.frames G).level d) ((Issue.trail P).S.side (m+1) n))
-- Selling thrice, epoch κ force.
lemma tender (hQ:ShellDate (AX:=AX) (l:=l) (p0:=p0) (TT:=TT) (κ:=κ) d V (m+1) Q) : ∃ v:ℂ,∃ Xl:Set Lotus.Wing,Xl.Finite ∧ XPre.Circuit Xl (U.deed N n m hm) d κ k' L (o (m+1)) ((A.B.a.clock.op m n).ratio.parent (o (m+1))) 1 (glyphSeed H N n f M' o V (m+1)) (glyphK H N n f M' o V (m+1)) (glyphK H N n f M' o V m) v (chanT G d p₁ l b q₀ Yx Y (u)) (chanF G d p₁ l b q₀ Yx u) (chanK G d p₁ Yx u):=by
    let τ:= rotationP F (R₁).p.order (R₁).p.power; let tA:= U.deed N n m hm; let S:= A.B.a.clock.op m n
    let c':= S.ratio.embed (o m); let Y':= (T).clock.hatBeta (m+1); have heq:y=Y:=beta_eq A.B.valid m; rw [← heq] -- only exponent powers uses hp.Height
    let u₀:= y^t'; let U₀:= Yx; let u':= orbitCost F
    obtain ⟨Yl,hY,hL⟩:= U.vacantPXC hm hG hr hκ d hd V Q hQ (hv.earned (m+1) (by omega) hm) hh hA f -- args
    obtain ⟨π⟩:= (P.choice.represents N n (m+1) hm).good.labels.moves M'.1 (S.ratio.embed (o m))
    obtain ⟨g',hv'⟩:= (U.port N m n hm|>.ranch.allocation.paid)
    let a' :ℂ:= ((Issue.trail P).S.block m|>.val:ℂ)^d
    have hAX:= sample_step H (N:=N) (d:=d) (m:=m); change (σ (m+1))=a'* (σ m) at hAX
    let z:= σ m
    have ht:= XPre.turning hL M' (o m) π (U.purses hG (n:=n) hm hd|>.honest) (U.preQtunes hm) ((hκ N m n hm).2 ▸ hv') (show Motion.scalar M' a'=a' from by unfold a' Motion.scalar; split<;>simp)
    have ht:= XPre.corpo_transport ht (σ (m+1)) (σ m) hAX
    have hec:c'=o (m+1):=hp.symm
    have hx: (S).ratio.parent (o (m+1))=o m:=by rw [← hec]; exact (S.ratio.embed_parent ..)
    let W':= Wing.labelRoute π
    -- avoid dependent rewrite π
    rw [show (A.B.a.clock.op m n).ratio.parent (o (m+1))= o m from hx]
    erw [show affine M'.1 (S.ratio.embed (o m)) 0= o (m+1) from (show affine M'.1 c' 0=c' by simp [affine]).trans hec,show affine M'.1 (o m) 0=o m by simp [affine]] at ht
    let χ:= glyphSeed H N n f M' o V; let χ':= glyphK H N n f M' o V
    have h1 :stepUp M' (S.ratio.embed (o m)) ((U₁).plays f|>.exponentialEntry 0 T₀ R₁) = stepUp M' (o (m+1)) ((U₁).plays f|>.exponentialEntry 0 T₀ R₁):=by rw [← hec]; rfl
    have h2 :floatUp M' (S.ratio.embed (o m)) (profile (R₁).activities ((U₁).plays f).forced)=floatUp M' (o (m+1)) (profile (R₁).activities ((U₁).plays f).forced):=by rw [← hec]; rfl
    -- κ lookups distinct variable. Rewrite S ratio.
    erw [h1,h2] at ht
    refine ⟨_,Set.image W' Yl,hY.image W', XPre.widened ht ?_ ?_ le_rfl ?_⟩
    all_goals
       let B0:= u₀; let z₀:= σ (m+1); let cc:= (F).coeffSize ((V.tone (m+1)).index f); let g:= payG G (X.p.profile I') (X.p.profile J) l d b; let s:= Real.sqrt (A.B.a.clock.forcedAllowance (m+1));
       have hh : ‖z₀‖*cc ≤ Yx:= U.cornerstone V f hv he m h hm.le TT hy (m+1) (m.le_succ) hm
       let A':= R₁; have hy: τ= rotationP F (X.p.profile (J)).order (X.p.profile (J)).power:=by
          have hp:(R₁).p=(T).budget (m+1):=P.choice.represents N n (m+1) hm|>.vac; unfold τ; rw [hp,Rain.jersey (A:=A) (m:=m+1)|>.1,Rain.jersey (A:=A) (m:=m+1)|>.2.1]
       have hr:0≤ τ:=zero_le_one.trans (rotation_one ..); have hy':= (T).fits.delayed (m+1); have hu:1≤y:=hy'.le; have hζ:0≤ u₀:=Real.rpow_nonneg (zero_le_one.trans hu) _; have hb:= Graces.glyphBound (T) (m+1); have his: s*(u₀+u₀)≤u₀+u₀:=mul_le_of_le_one_left (add_nonneg hζ hζ) hb.2
       let i':=u'; have hi:0≤ i':= zero_le_one.trans (orbitCost_one_le F); have hv₀:0≤ cc:=Work.G08.size_nonneg ..
    · unfold chanT burnT; rw [← hy]; let t0:= g.beam+2*(y+B0+(B0+B0)); have he:0 ≤ t0:= add_nonneg g.future (mul_nonneg zero_le_two (add_nonneg (add_nonneg (zero_le_one.trans hu) hζ) (add_nonneg hζ hζ)))
      let f0:= g.beam+2*(y+B0+s*(B0+B0)); have hf:f0≤t0:= add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl his) zero_le_two)
      change ‖z₀‖*(τ*(i'*cc*(τ*f0))) ≤ _; rw [show ‖z₀‖*(τ*(i'*cc*(τ*f0)))= (‖z₀‖*cc)*(τ*(i'*(τ*f0))) from by ring]; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf hr) hi) hr) (mul_nonneg (norm_nonneg _) hv₀)).trans (mul_le_mul_of_nonneg_right hh (mul_nonneg hr (mul_nonneg hi (mul_nonneg hr he))))
    · have hz0 :1 ≤ ‖a'‖:=by change 1 ≤ ‖((↑((Issue.trail P).S.block m).val:ℂ)^d)‖; rw [norm_pow, Complex.norm_natCast]; exact one_le_pow₀ (by exact_mod_cast (Issue.trail P).S.block m|>.property)
      have hx: ‖z‖ ≤ ‖z₀‖:= (le_mul_of_one_le_left (norm_nonneg _) hz0).trans (show _= ‖z₀‖ from (by unfold z₀; rw [hAX,norm_mul])).le
      have hb' : ‖z‖*cc ≤Yx:= (mul_le_mul_of_nonneg_right hx hv₀).trans hh
      let Y0:= (X.p.profile (J)).columns; have hE:(A.B.a.params (m+1)).columns= Y0:=by rw [params_eq A.B.valid]
      let t0:= g.grant+g.canopy*(Y0+(B0+B0)); let f0:= g.grant+g.canopy*(Y0+s*(B0+B0)); have hf:f0 ≤ t0:= add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl his) g.crown); have he:0≤ t0:= add_nonneg g.pole (mul_nonneg g.crown (add_nonneg (zero_le_one.trans (X.p.profile J).columns_ge) (add_nonneg hζ hζ)))
      rw [hE]; change ‖z‖*(i'*cc*f0)≤_; rw [show ‖z‖*(i'*cc*f0)=(‖z‖*cc)*(i'*f0) from by ring]; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf hi) (mul_nonneg (norm_nonneg _) hv₀)).trans (mul_le_mul_of_nonneg_right hb' (mul_nonneg hi he))
    unfold chanK rateT; rw [← hy]; let t0:=2*(B0+(B0+B0)); let f0:=2*(B0+s*(B0+B0)); have he:0 ≤ t0:= mul_nonneg zero_le_two (add_nonneg hζ (add_nonneg hζ hζ)); have hf:f0≤t0:= mul_le_mul_of_nonneg_left (add_le_add le_rfl his) zero_le_two
    change ‖z₀‖*(τ*(i'*cc*(τ*f0))) ≤ _; rw [show ‖z₀‖*(τ*(i'*cc*(τ*f0)))= (‖z₀‖*cc)*(τ*(i'*(τ*f0))) from by ring]; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf hr) hi) hr) (mul_nonneg (norm_nonneg _) hv₀)).trans (mul_le_mul_of_nonneg_right hh (mul_nonneg hr (mul_nonneg hi (mul_nonneg hr he))))
end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
