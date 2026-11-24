import YM.Integration.WilsonOriginalSeparatedCourse
import YM.WilsonCoeffUV.Emit.Cumulative

/-! Keep the actual pre-block Schur constant of the original marked tokenizer on its selected Realm. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalOpticalSpot
open Function Filter Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonLimitConstruction
open PowerSeries Blue Mer Embroider Embroider.Canvas Soil Laurent Cosmos Gauge Power Matrix Tree Exterior
open AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Metric Shard Realm PathCost
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Polestar Supply Ticket Flooring
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {p : Sheet G} {F' : ℕ → ℕ} {Y : Rolls p}
  {Ω : Protection Y} {V : Delays Ω} {o : Bar V} {b' : Supply.Wait o}
  {A : Levels G} {Ñ : ChartRatio G} {e : ℕ}

/-- The actual Visits construction uses the subsequent tokenizer's outlet as its incoming width. -/
theorem exact_marks (pL : Paid b' A) (i : ℕ)
    (b : ∀ j ≥ i, 5 ≤ A.clock.J (j+1) ∧ e ≤ F' (A.clock.J (j+1)))
    (d : ℕ → Gear G → ℝ) (z : preBoard p F' ≤ p.floorL)
    (v : coolTax F' p Y Ñ d ≤ V.betaEntry) :
    Nonempty {I : Marks A Ñ e i (zz A) // ∀ j (h : i ≤ j),
      d (F' (A.clock.J (j+1))) (I.mass j h).gear ≤ zz A j ∧
      (I.mass j h).σ = crestM A j (b j h).1 ∧
      (I.mass j h).s = (raySmall G A.clock.kernel _ _ (A.clock.adm j) (b j h).1).s ∧
      (I.mass j h).preB = (raySmall G A.clock.kernel _ _ (A.clock.adm j) (b j h).1).preB ∧
      (I.mass j h).past = crestM A (j+1) (upstairs A (j+1) (b j h).1)} := by
    have ht j : A.S.block j=Y.L (A.clock.J (j+1)):=by rw [←A.fits.sameFactor,pL.lengths]
    have hu j (h:i≤ j): cottage A j (F' (A.clock.J (j+1))) (b j h).1:=by
        let k:= A.clock.J (j+1); have he: preBoard p F' k ≤ (A.S.block j).val:= le_trans (le_trans (z k) (Y.large k).need) (le_of_eq (congr_arg Subtype.val (ht j).symm)); exact (eventually_atTop.mp (growL G p.kernel (F' k) k)).choose_spec _ he A j pL.kernel rfl rfl (b j h).1
    let I j (h:i≤ j):= spot A j Ñ (b j h).1 (hu j h)
    have he j (h:i≤ j): Escrow (I j h) e (zz A j)∧ d (F' (A.clock.J (j+1))) (I j h).gear ≤ zz A j:=by
        let k:=A.clock.J (j+1); let U:= eventually_atTop.mp (growers p.kernel (Y.L k) k (F' k) Ñ (d (F' k))); let C':= U.choose
        have hQ : Real.exp (Real.exp C') ≤ A.clock.hatBeta j:=le_trans (v k) (pL.pays _)
        have hx : C'≤ zz A j:=by have h:=Real.log_le_log (Real.exp_pos _) hQ; rw [Real.log_exp] at h; have ht:=Real.log_le_log (Real.exp_pos _) h; rw [Real.log_exp] at ht; exact ht.trans (le_add_of_nonneg_left zero_le_one)
        obtain ⟨hv,f⟩:= U.choose_spec _ hx A j pL.kernel rfl (ht j) _ (hu j h); exact ⟨further hv (b j h).2 le_rfl, f⟩
    exact ⟨⟨⟨I,fun i p=>(he i p).1,fun _ _=> le_rfl⟩,fun j h=>⟨(he j h).2,rfl,rfl,rfl,rfl⟩⟩⟩


section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {X D : ι → ℕ}
variable {b h l i : ℕ} {D' : ℕ → ℕ} {P : Sheet G} {Y : Rolls P}
  {Ω : Protection Y} {V : Delays Ω} {o : Bar V} {b' : Supply.Wait o}
private theorem insured_marks (H:Hol G)(M:Master H)(u:∀ i,X i<D i)(g:G.Simple)(q:LocalRatio Ñ) (pL:floors G P.kernel F' ≤ P.floorL)(zL:(fun i=>sharp H M P.kernel Ñ i (F' i) (D' i))≤ P.floorL)(zS:preBoard P F'≤ P.floorL)(a:Paid b' A)(s:Ticket.voucher Y F' Ñ≤ V.betaEntry)(x:(fun j=>tickZ H M P.kernel Ñ (Y.L j) (F' j) (D' j) j)≤ V.betaEntry) (v:ℕ→Gear G →ℝ)(hY: coolTax F' P Y Ñ v ≤ V.betaEntry)
   (t:∀ j≥i, let k:= A.clock.J (j+1); let n:=F' k; 5 ≤ k ∧ e+1 ≤ n ∧ (∀ s:ι,X s+1≤ k-2 ∧ D s ≤ D' k) ∧ censusV G D X b h e≤ v n):
   ∃ T: Realm G (e+1) Credit.leanC, T.draws=A∧ T.paid=Ñ∧T.y=zz A∧T.anchor=i∧ Cloze D X T Credit.leanC∧ Insure b h T Credit.leanC ∧ Nonempty (Tribe T H Credit.leanC Credit.leanC (counter H M X D u))∧ ∀ j(hb:i≤j)(p:T.anchor≤j), (T.mint j p).σ=crestM A j (t j hb).1 ∧
      (T.mint j p).s = (raySmall G A.clock.kernel _ _ (A.clock.adm j) (t j hb).1).s ∧
      (T.mint j p).preB = (raySmall G A.clock.kernel _ _ (A.clock.adm j) (t j hb).1).preB ∧
      (T.mint j p).past = crestM A (j+1) (upstairs A (j+1) (t j hb).1) ∧
      v (F' (A.clock.J (j+1))) (T.mint j p).gear ≤ T.cash Credit.leanC j:=by
   obtain ⟨N,hN⟩:= exact_marks (e:=e+1) a i (fun j p=>⟨(t j p).1,(t j p).2.1⟩) v zS hY
   obtain ⟨hx,ht,_⟩:= install_awards g q pL a s i (e+1) (fun j p=>⟨(t j p).1,(t j p).2.1⟩)
   let T: Realm G (e+1) Credit.leanC:= ⟨A,Ñ,g,q,i, zz A,hx,ht,N.mass,N.overlap, fun i v=> by rw [Credit.lean_cost]; exact N.takes i v⟩
   have he j (p:T.anchor≤ j): (T.mint j p).σ=crestM A j (t j p).1∧v (F' (A.clock.J (j+1))) (T.mint j p).gear ≤ T.cash Credit.leanC j:= by rw [Realm.cash,Credit.lean_cost]; exact ⟨(hN j p).2.1,(hN j p).1⟩
   have hu j (p:T.anchor≤ j): tellerR G D X e (T.mint j p).gear ≤ T.cash Credit.leanC j∧ stow G h b (e+1) (T.mint j p).gear ≤ T.cash Credit.leanC j:= max_le_iff.mp (le_trans ((t j p).2.2.2 _) (he j p).2)
   refine ⟨T,rfl,rfl,rfl,rfl,⟨fun j p=>(max_le_iff.mp (show max _ _ ≤_ from (hu j p).1)).1,fun j p=>(max_le_iff.mp (show max _ _ ≤ _ from (hu j p).1)).2⟩, insured b h T (fun j p=>(hu j p).2),⟨fun y=>?_⟩,fun j _ p=> ⟨(he j p).1,(hN j p).2.2.1,(hN j p).2.2.2.1,(hN j p).2.2.2.2,(he j p).2⟩ ⟩
   apply Classical.choice; obtain ⟨Y,hM,x',y',f,c⟩:= fixtures_paid H M g q pL zL a s x (u y) e i (fun j v=> ⟨(t j v).1,((t j v).2.2.1 y).1,(t j v).2.1,((t j v).2.2.1 y).2⟩)
   let P :PassportC H T (counter H M X D u y) Credit.leanC Credit.leanC:= ⟨Y,hM,x',y',f⟩
   refine ⟨P,fun j v=>?_⟩; obtain ⟨p,b,x,t',g⟩:= c j (f.symm ▸ v); rw [(he j v).1,show P.f.arch.angle j _ =_ from g]; exact le_rfl

end
section
variable {b h l i : ℕ} {D' : ℕ → ℕ} {P : Sheet G} {Y : Rolls P}
  {Ω : Protection Y} {V : Delays Ω} {o : Bar V} {b' : Supply.Wait o}
private theorem mature {i' h': Fin l→ℕ}(H:Hol G)(M:Master H)(u:∀ i,i' i<h' i)(g:G.Simple)(q:LocalRatio Ñ)
    (pL:floors G P.kernel F' ≤ P.floorL)(zL:(fun i=>sharp H M P.kernel Ñ i (F' i) (F' i))≤ P.floorL)
    (zS:preBoard P F'≤ P.floorL)(a:Paid b' A)(s:Ticket.voucher Y F' Ñ≤ V.betaEntry)(x:(fun j=>tickZ H M P.kernel Ñ (Y.L j) (F' j) (F' j) j)≤ V.betaEntry)
    (v:ℕ→Gear G →ℝ)(hY: coolTax F' P Y Ñ (diary G⊔ v) ≤ V.betaEntry) (y:Tendsto F' atTop atTop)(b h e:ℕ): ∀ᶠ i:ℕ in atTop,
    ∃ T: Realm G (e+1) Credit.leanC, T.draws=A∧ T.paid=Ñ∧T.y=zz A∧T.anchor=i∧ Cloze h' i' T Credit.leanC
    ∧ Insure b h T Credit.leanC ∧ Nonempty (Tribe T H Credit.leanC Credit.leanC (counter H M i' h' u))
    ∧ ∀ j(_:i≤j)(t:T.anchor≤j), ∃ z:5≤A.clock.J (j+1), (T.mint j t).σ=crestM A j z ∧
    (T.mint j t).s = (raySmall G A.clock.kernel _ _ (A.clock.adm j) z).s ∧
    (T.mint j t).preB = (raySmall G A.clock.kernel _ _ (A.clock.adm j) z).preB ∧
    (T.mint j t).past = crestM A (j+1) (upstairs A (j+1) z) ∧ v (F' (A.clock.J (j+1)))
    (T.mint j t).gear ≤ T.cash Credit.leanC j:= by
   have he:Tendsto (fun i=>A.clock.J (i+1)) atTop atTop:=A.fits.deep.comp (tendsto_add_atTop_nat 1); let f:= F' ∘ fun i => A.clock.J (i+1); have hp:Tendsto f atTop atTop:=y.comp he
   obtain ⟨L,t⟩:= (eventually_atTop.mp ((he.eventually_ge_atTop 5).and ((hp.eventually_ge_atTop (b+h+e+1+l)).and (eventually_all.mpr fun j:Fin l=> (he.eventually_ge_atTop (i' j+3)).and (hp.eventually_ge_atTop (h' j)))))); apply (eventually_ge_atTop L).mono; intro i p
   have hh : ∀ j ≥ i, let k:= A.clock.J (j+1); let n:=F' k; 5 ≤ k ∧ e+1≤ n ∧ (∀ s:Fin l,i' s+1≤k-2∧ h' s≤ n) ∧ censusV G h' i' b h e ≤ (diary G⊔v) n :=by
     intro j v'; let N:= A.clock.J (j+1); obtain ⟨hV,z,d⟩:= t j (p.trans v'); dsimp only [f,Function.comp_apply] at z d; refine ⟨hV,by omega,fun q=>by specialize d q; omega,?_⟩
     exact le_trans (depot G (F' N) l b h e h' i' (by exact le_trans (Nat.le_add_left ..) z) (by unfold N; omega) (by unfold N; omega) (by unfold N; omega) (fun i => (d i).2) (fun j=> (u j).le.trans (d j).2)) (le_sup_left (b:=v (F' N)))
   obtain ⟨T,h₁,h₂,h₃,h₄,t1,t2,t3,t4⟩:= insured_marks H M u g q pL zL zS a s x (e:=e) (i:=i) _ hY (b:=b) (h:=h) hh
   refine ⟨T,h₁,h₂,h₃,h₄,t1,t2,t3,fun j p t=>?_⟩; have h₀:=t4 j p t; exact ⟨_,h₀.1,h₀.2.1,h₀.2.2.1,h₀.2.2.2.1,le_trans (le_max_right ..) h₀.2.2.2.2⟩
end

/-- A single genuine realm keeps the selected print gear, its two width
coordinates, the charged rooted marked data and the unmarked clock. -/
theorem realm (R : Run G) (simple : G.Simple) (v : ℕ → Gear G → ℝ)
    (paid : FundedMarkedCoverRows.prices v R.kit) (n : ℕ) (k D : Fin n → ℕ)
    (hk : ∀ a, k a < D a) (e b h : ℕ) : ∀ᶠ m : ℕ in atTop,
    ∃ Q : Realm G (e+1) Credit.leanC, Q.draws = R.family.path.levels ∧ Q.paid = R.metals.O ∧
      Q.y = zz R.family.path.levels ∧ Q.anchor = m ∧
      Cloze D k Q Credit.leanC ∧ Insure b h Q Credit.leanC ∧
      Nonempty (Tribe Q (hol G) Credit.leanC Credit.leanC (counter (hol G) (primes G) k D hk)) ∧
      ∀ j, m ≤ j → ∀ hj : Q.anchor ≤ j, let A := R.family.path.levels
        ∃ z : 5 ≤ A.clock.J (j+1), (Q.mint j hj).σ = crestM A j z ∧
          (Q.mint j hj).s = (raySmall G A.clock.kernel _ _ (A.clock.adm j) z).s ∧
          (Q.mint j hj).preB = (raySmall G A.clock.kernel _ _ (A.clock.adm j) z).preB ∧
          (Q.mint j hj).past = crestM A (j+1) (upstairs A (j+1) z) ∧
          v (A.clock.J (j+1)) (Q.mint j hj).gear ≤ Q.cash Credit.leanC j := by
  obtain ⟨chartEq, hfloor, hwidth, hkernel, hmark⟩ := paid
  have awards := reported (hol G) (primes G) hfloor hkernel
  rw [chartEq]
  exact mature (hol G) (primes G) hk simple (chart_ok G) awards.ink awards.rise
    hwidth R.alloy.B.valid awards.fg awards.hg v hmark tendsto_id b h e

end YM.Integration.WilsonOriginalOpticalSpot
end

