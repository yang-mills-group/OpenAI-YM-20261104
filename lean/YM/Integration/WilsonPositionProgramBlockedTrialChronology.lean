import YM.Integration.WilsonPositionProgramNominatedPin
import YM.Integration.WilsonPositionProgramHearthBirth
/-! Newly planted marked sections at a retained date on an already evolved Wilson
vacuum. The earlier ordinary joint row is one input to the next joint Wick step.
The ultraviolet date of that vacuum stays fixed throughout this calculation. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
namespace YM.Integration.WilsonPositionProgramBlockedTrialChronology
open Filter Finset Lattice Wilson RG RG.Supply Precision Labels Source
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard WilsonCoeffUV.Embroider WilsonCoeffUV.Soil
open Gauge AnalyticNext.QuarticMatch.Sheets Work.F08 Exterior Next.Free Tree Planned.PrimaryIntegral295 Place Carrier WardBin
open WilsonCoeffUV.Fountain
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open scoped Classical BigOperators
variable {G:Gauge}{a a' h D k u e:ℕ}
def old (R:Run G)(Q:Fin (a+1)→SealR G)(X:Herit Q)(φ:Wilt Q)(m N K:ℕ)(y:ℝ)(c:CellR):Era G ℝ:=
  let L:=R.family.path.levels
  let O:=R.metals.O
  cruises L O N (capP Q) N K (locale c (HearthC Q L O φ (normalized L O Q X m N) m N N y))
def fresh (R:Run G)(Q:Fin (a+1)→SealR G)(X:Herit Q)(φ:Wilt Q)(K:ℕ)(y:ℝ)(c:CellR):Era G ℝ:=
  locale c (HearthC Q R.family.path.levels R.metals.O φ X K K K y)
def response (R:Run G)(N K j b:ℕ)(U V:Era G ℝ):Era G ℝ:=
  cruises R.family.path.levels R.metals.O N b K j (agateV U V)

theorem received (R:Run G)(simple:G.Simple)(legal:LocalRatio R.metals.O)
    {N K j k₀ k₁:ℕ}(seen:j<K)(high:K≤N){U V:Era G ℝ}(hu:Auth k₀ U)(hv:Auth k₁ V):
    let L:=R.family.path.levels
    let O:=R.metals.O
    let Z:=response R N K (j+1) (k₀+k₁) U V
    Auth (k₀+k₁) (response R N K j (k₀+k₁) U V) ∧
    (∀ n:Side,flash ((response R N K K (k₀+k₁) U V).1 n)=flash (U.1 n)*flash (V.1 n)) ∧
    (∀ n:Side, let p:=ll L j; let op:=L.clock.kernel
      (response R N K j (k₀+k₁) U V).1 n=
        Blue.mix (ratioHigh L O N j)
          (reed (stepAt p op n) (xree p op n) (freeForms L N (j+1)) (roam L N j n)
            O ((story L O N (j+1)).1 (n*p.L)) (k₀+k₁) (Z.1 (n*p.L)))):=by
  intro L O Z
  refine ⟨cruising L simple legal seen.le high (hu.manor hv),?_,?_⟩
  · intro n;unfold response;rw [cruises_top]
    exact woadap _ _ (finite_shell (hu.span _)) (finite_shell (hv.span _))
  · intro n p op
    unfold response
    rw [cruises_sub _ _ _ _ _ seen]
    rfl

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices v R.kit)
    (big:h<D)(rails:Rails h k u e)(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)
    (l' d':Fin (a'+1)→ℕ)(fit':∀i,l' i<d' i)
    (cap:capP (deck (G:=G) l d fit)≤k)(cap':capP (deck (G:=G) l' d' fit')≤k):
    let A:=deck (G:=G) l d fit;let B:=deck (G:=G) l' d' fit'
    ∀ᶠ f:ℕ in atTop,∀m K N:ℕ,f ≤ m → m ≤ K → K ≤ N →
    ∀X:Herit A,∀Y:Herit B,∀φ:Wilt A,∀ψ:Wilt B,∀y y' c c',
      let U:=old R A X φ m N K y c;let V:=fresh R B Y ψ K y' c'
      Auth (capP A) U ∧ Auth (capP B) V ∧
      (∀b:ℕ,b ≤ K → Auth (capP A+capP B) (response R N K b (capP A+capP B) U V)) ∧
      (∀n:Side,flash ((response R N K K (capP A+capP B) U V).1 n)=flash (U.1 n)*flash (V.1 n)):=by
  intro A B
  filter_upwards [WilsonMarkedIndependentNormalizedElection.original R simple v paid big rails l d fit cap,
    WilsonMarkedIndependentNormalizedElection.original R simple v paid big rails l' d' fit' cap']
    with f a b
  obtain ⟨W,T,lv,rt,_,first,_,_,_,_,enrolled⟩:=a
  obtain ⟨W',T',lv',rt',_,first',_,_,_,_,enrolled'⟩:=b
  intro m K N fm mK KN X Y φ ψ y y' c c' U V
  let L:=R.family.path.levels;let O:=R.metals.O
  have legal:LocalRatio R.metals.O:=rt ▸ T.L.V.green
  have hs:Auth (capP A) (HearthC A L O φ (normalized L O A X m N) m N N y):=by
    have h':T.L.V.anchor≤N:=first ▸ (fm.trans mK).trans KN
    have h'':=Hearth_enter (m:=m) (y:=y) enrolled φ (normalized L O A X m N) h' (le_refl N)
    rwa [lv,rt] at h''
  have hu:Auth (capP A) U:=cruising L simple legal KN (le_refl N) (locale_val _ hs c)
  have hv:Auth (capP B) V:=by
    have h':T'.L.V.anchor≤K:=first' ▸ fm.trans mK
    have h'':=Hearth_enter (m:=K) (y:=y') enrolled' ψ Y h' (le_refl K)
    rw [lv',rt'] at h''
    exact locale_val _ h'' c'
  refine ⟨hu,hv,fun b le=>cruising L simple legal le KN (hu.manor hv),?_⟩
  intro n;unfold response;rw [cruises_top]
  exact woadap _ _ (finite_shell (hu.span _)) (finite_shell (hv.span _))
end YM.Integration.WilsonPositionProgramBlockedTrialChronology
end
