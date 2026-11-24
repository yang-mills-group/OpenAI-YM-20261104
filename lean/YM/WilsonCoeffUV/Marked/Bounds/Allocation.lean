import YM.WilsonCoeffUV.Marked.Bounds.PreWidth
/-!
# Width and timing costs can be demanded BEFORE using Buds

For static finite list. `F',D'` even moving horizons with promise ramp, at
all future steps need the ECC promise; other slot/enlarging ideals can be
prebought by rerunning Obligation before final choices. Doesn't assert a
matching on particular `p` without comparison floors/delays.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Cadenza
open Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Metric Shard Realm PathCost
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Polestar Supply Ticket
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {c f:Side}{ι U:Type}{J I T:Finset ι}{D k K':ι→ℕ}{i j i' j' a e r h N n m b l:ℕ}{G:Gauge}{σ τ u g B C z ρ:ℝ}{E W V' U':Credit}{K:KernelChoices}
variable {R : Realm G (e+1) E}{H:Hol G}{Q:ι→SealR G}
variable {p:Sheet G}{F' D':ℕ→ℕ}{Y:Rolls p}{Ω:Protection Y}{V:Delays Ω}{o:Bar V}{b':Supply.Wait o}{A:Levels G}{Ñ:ChartRatio G}

variable [Fintype ι][DecidableEq ι]
def tellerR (G:Gauge)(D k:ι→ℕ)(e:ℕ)(I:Gear G):= max (shrinePost G D k e I) (elixir I-I.σ)⁻¹
lemma scheduleL (pL:Paid b' A)(i:ℕ)(b:∀ i'≥i, 5≤ A.clock.J (i'+1) ∧ e+1≤ F' (A.clock.J (i'+1)))(zL: preBoard p F'≤ p.floorL)(vL: coolTax F' p Y Ñ (fun _=>tellerR G D k e) ≤ V.betaEntry) (g:G.Simple)(h:LocalRatio Ñ)(sL:floors G p.kernel F'≤ p.floorL)(z:voucher Y F' Ñ ≤ V.betaEntry):
    ∃ R:Realm G (e+1) Credit.leanC, Cloze D k R Credit.leanC∧R.draws=A∧R.paid=Ñ∧R.y=zz A∧R.anchor=i∧∀ j (hb:i ≤ j) (h:R.anchor ≤ j), (R.mint j h).σ=crestM A j (b j hb).1:=by
   obtain ⟨M,hM⟩:= Venice pL i b _ zL vL; obtain ⟨hP,hS,_⟩:=install_awards g h sL pL z _ _ b
   let R:Realm G (e+1) Credit.leanC:= ⟨A,Ñ,g,h,i, zz A,hP,hS,M.mass,M.overlap,fun i v=> by rw [Credit.lean_cost]; exact M.takes i v⟩
   have ht j (p:R.anchor ≤ j): max (shrinePost G D k e (R.mint j p).gear) (elixir (R.mint j p).gear- (R.mint j p).σ)⁻¹ ≤ R.cash Credit.leanC j:=by rw [cash,Credit.lean_cost]; exact (hM j p).1
   exact ⟨R,⟨fun j p=> (max_le_iff.mp (ht j p)).1, fun j p=> (max_le_iff.mp (ht j p)).2⟩,rfl,rfl,rfl,rfl, fun j _ p=>(hM j p).2⟩

-- identical stencil dictionary for any supplied H; `K-ζ` convention pinned
abbrev counter (H:Hol G)(R:Master H)(h D:ι→ℕ)(u:∀ i,h i<D i)(i:ι): SealR G:=⟨h i,R.F (h i),D i,R.T (h i),u i⟩
theorem awarded (H:Hol G)(R:Master H)(u:∀ i,k i<D i)(g:G.Simple)(h:LocalRatio Ñ)(pL:floors G p.kernel F'≤ p.floorL)(zL:(fun i=>sharp H R p.kernel Ñ i (F' i) (D' i)) ≤ p.floorL)(w: preBoard p F'≤ p.floorL)(a:Paid b' A)(hp:voucher Y F' Ñ ≤ V.betaEntry)(hz:(fun j=>tickZ H R p.kernel Ñ (Y.L j) (F' j) (D' j) j)≤ V.betaEntry)(v: coolTax F' p Y Ñ (fun _=>tellerR G D k e) ≤ V.betaEntry)
   (b:∀ j≥i, let x:= A.clock.J (j+1); 5≤x ∧ e+1≤ F' x ∧ ∀ s:ι,k s+1≤ x-2 ∧ D s≤ D' x) : ∃ T:Realm G (e+1) Credit.leanC, T.draws=A∧T.paid=Ñ∧ T.y=zz A∧T.anchor=i∧Cloze D k T Credit.leanC∧Nonempty (Tribe T H Credit.leanC Credit.leanC (counter H R k D u)):=by
   obtain ⟨T,hT,he,hb,hu,ht,hv⟩:=scheduleL a i (fun j v=>⟨(b j v).1,(b j v).2.1⟩) w v g h pL hp
   refine ⟨T,he,hb,hu,ht,hT, ⟨fun s=>?_⟩⟩; apply Classical.choice
   obtain ⟨M,hM,x,y,f,c⟩:= fixtures_paid H R g h pL zL a hp hz (u s) e i (fun j v=> ⟨(b j v).1,((b j v).2.2 s).1,(b j v).2.1,((b j v).2.2 s).2⟩)
   let L:= T.anchor
   let P: PassportC H T (counter H R k D u s) Credit.leanC Credit.leanC := ⟨M,hM.trans he.symm,x.trans hb.symm,y.trans hu.symm,f.trans ht.symm⟩
   refine ⟨P,fun j a=>?_⟩
   let h:= (P.tap.symm ▸ a : P.f.arch.V.anchor ≤ j)
   obtain ⟨z,b,s,w,H'⟩:= c j h
   rw [hv j (ht ▸ a), show P.f.arch.angle j h=_ from H']; exact le_rfl
end YM.WilsonCoeffUV.Wheel.Cadenza
