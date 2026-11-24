import YM.Integration.WilsonOlderFreshGraphSubpower

/-! One aperture-capped original school for every finite source loan and
every prescribed finite order. The grants activated at stage x are finite
and fixed before the kernel price and block length are chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphAllStages
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Mentor Push.PriceCompiler
open Primer AllOrder AllOrder.Ink AllOrder.Floe Primitives.TwoWave QuadraticLocal.Poetry
open WilsonOlderFreshGraphSchool WilsonFundedWindowMenu WilsonWindowJointPurchase
open WilsonOlderFreshGraphPainter
open scoped Topology ENNReal BigOperators Classical

open WilsonOlderFreshGraphCompiler

open WilsonOlderFreshGraphMatrixPrice

structure Query where
  letter:Loan
  order:ℕ

namespace Query
def code (S:Query):ℕ×ℕ×ℕ×ℕ:=(S.letter.e,S.letter.r,S.letter.toll,S.order)

lemma injective:Function.Injective code:=by
  rintro ⟨⟨e,r,t,h,h'⟩,q⟩ ⟨⟨e',r',t',k,k'⟩,q'⟩
  simp only [code,Prod.mk.injEq]
  rintro ⟨rfl,rfl,rfl,rfl⟩
  rfl

instance : Countable Query:=injective.countable
noncomputable instance : Encodable Query:=Encodable.ofCountable Query

def name (S:Query):ℕ:=Encodable.encode S
def catalogue (x:ℕ):Query:=(Encodable.decode (α:=Query) x).getD ⟨⟨0,0,1,by decide,by decide⟩,0⟩
lemma attends (S:Query):catalogue S.name=S:=by simp [catalogue,name]
def letters (S:Query):Unit→Loan:=fun _=>S.letter

def orderMenu (G:Gauge)(S:Query):WilsonOlderFreshGraphSchool.Menu:=
  WilsonOlderFreshGraphMatrixPrice.menu G S.letters S.letter.toll S.order rfl

end Query

def menu (G:Gauge):WilsonOlderFreshGraphSchool.Menu where
  width:=fun A p K k x=>Finset.univ.inf' Finset.univ_nonempty
    (fun n:Fin (x+1)=>((Query.catalogue n.val).orderMenu G).width A p K k x)
  positive:=fun A p K k x=> (Finset.lt_inf'_iff _).2
    (fun j _=>((Query.catalogue j.val).orderMenu G).positive A p K k x)
  shell:=fun _=>1
  cost:=fun _=>zero_lt_one

lemma offered {G:Gauge} {x k:ℕ} (S:Query)(live:S.name ≤ x)
    (A:ℕ→Stage)(p:MapPrices)(K:KernelChoices):
    (menu G).width A p K k x ≤ (S.orderMenu G).width A p K k x:=by
  let n:Fin (x+1):=⟨S.name,Nat.lt_succ_of_le live⟩
  unfold menu
  have h:=Finset.inf'_le (f:=fun m:Fin (x+1)=>((Query.catalogue m.val).orderMenu G).width A p K k x)
    (Finset.mem_univ n)
  simpa [n,Query.attends] using h

theorem prepared {G:Gauge} (simple:G.Simple){φ:ℕ→ℕ} (law:VowsR.LawScroll G φ) (U:ℕ→ℕ)
    (ready:∀(s:Sheet G)(q:MapPrices),WilsonWindowBookPurchase.Permitted law s (ThroughLaunch.raging s q)):
    AllPrices (Together (@WilsonOlderFreshGraphSchool.grant G φ (menu G) simple (jointLaw law))
      (@WilsonWindowFormalPurchase.Canonical G U)):=fun s q=>
  joint (WilsonOlderFreshGraphSchool.before_period (menu G) simple (jointLaw law)
    (fun s q=>WilsonWindowVacuumLaws.both (ready s q) (WilsonPhysicalHistoryPriorSelection.permitted φ s _)) s q)
    (WilsonWindowFormalPurchase.prepaid U s _)

theorem original {G:Gauge} (simple:G.Simple) (R:Run G) {φ U:ℕ→ℕ} (law:VowsR.LawScroll G φ)
    (purchase:Together (@WilsonOlderFreshGraphSchool.grant G φ (menu G) simple (jointLaw law))
      (@WilsonWindowFormalPurchase.Canonical G U) R.kit):
    let H:=roots (menu G) simple R.metals.p R.metals.K
    (∃ B,VowsR.Chamber law R.kit H (rollTab (menu G) simple R.metals R.rolls) B) ∧
    ∀(S:Query)(b k:ℕ),k ≤ R.alloy.B.a.clock.J (b+1)→1 ≤ Burn.horizon k→
      S.name ≤ R.alloy.B.a.clock.J (b+1)→
      let i:=R.alloy.B.a.clock.J (b+1)
      let σ:=Agenda.seed H φ (Burn.horizon k) i
      let K:=R.metals.p.kernel
      2*σ ≤ strip S.letters S.order (WilsonOlderFreshGraphPainter.width G K S.letter.toll S.order i) ∧
      (1+(printer G S.letters S.letter.toll S.order rfl K i).cap)^2 ≤ Real.log (R.alloy.B.a.clock.hatBeta (b+1)):=by
  intro H
  obtain ⟨⟨books,school⟩,gated⟩:=WilsonOlderFreshGraphSchool.on_run (menu G) simple (jointLaw law) R purchase.1
  have before:WilsonPhysicalHistoryPriorAperture.Paid R.rolls H φ R.alloy.delay:=school.obligation.2
  refine ⟨⟨books,{school with obligation:=school.obligation.1}⟩,?_⟩
  intro S b k fit hk live i σ K
  let v:=strip S.letters S.order (WilsonOlderFreshGraphPainter.width G K S.letter.toll S.order i)
  let g:=(printer G S.letters S.letter.toll S.order rfl K i).cap
  have σpos:0<σ:=Agenda.stem H φ (Burn.horizon k) i
  have g0:0≤g:=(printer G S.letters S.letter.toll S.order rfl K i).positive
  have hg:0<1+g:=by linarith
  have bound:=gated (Burn.horizon k) i hk
  have sub:=offered (G:=G) (k:=Burn.horizon k) S live R.metals.p.profile R.metals.K K
  change σ ≤ (menu G).width R.metals.p.profile R.metals.K K (Burn.horizon k) i/(16*1) at bound
  change (menu G).width R.metals.p.profile R.metals.K K (Burn.horizon k) i ≤ min v (1+g)⁻¹ at sub
  have hA:=min_le_left v (1+g)⁻¹
  have hG:=min_le_right v (1+g)⁻¹
  refine ⟨by change 2*σ ≤ v;linarith,?_⟩
  have inv:σ ≤ (1+g)⁻¹:=by linarith
  have fees:1+g ≤ σ⁻¹:=(le_inv_comm₀ hg σpos).mpr inv
  exact (pow_le_pow_left₀ hg.le fees 2).trans
    (WilsonPhysicalHistoryPriorAperture.on_run simple R H φ before b k fit)
end YM.Integration.WilsonOlderFreshGraphAllStages
end
