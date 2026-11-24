import YM.WilsonCoeffUV.Marked.Bounds.Output
import YM.WilsonCoeffUV.Root.UV.FrameSupply
/-!
# Mixed schedule on every order (can also enroll single demands)

Draws SAME as accepted context and physical labels as provided. Additional
width gates paid BEFORE lattice choices via decreased glint for unmarked
used with exponential models; nothing inferred about H plateau of given F
without these decisions.
 -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Cadenza
open Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Metric Shard Realm PathCost
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Polestar
open Supply Ticket
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {c f:Side}{ι U:Type}{J I T:Finset ι}{D k K':ι→ℕ}{i j i' j' a e r h N n m b l:ℕ}{G:Gauge}{σ τ u g B C z ρ:ℝ}{E W V' U':Credit}{K:KernelChoices}
variable {R : Realm G (e+1) E}{H:Hol G}{Q:ι→SealR G}

-- generic twin pricing before arc

def raySmall (G:Gauge)(K:KernelChoices)(i j:ℕ)(hp:4 ≤ i)(ht:5 ≤ j): Tokenizer K G i j:=by
    let T:= cue G K i j hp ht
    let s:= saffron G K i j hp ht
    exact { T with s:=s, sigma:=safron_nn G K i j hp ht, port:=fun A m p t u=> Glint.shrinks _ _ (T.port A m p t u) (le_trans (min_le_left ..) T.o_lt.le) }

def cottage (A:Levels G)(m n)(h:5 ≤ A.clock.J (m+1)):= Craft (raySmall G A.clock.kernel (A.clock.J m) (A.clock.J (m+1)) (A.clock.adm _) h) (raySmall G A.clock.kernel (A.clock.J (m+1)) (A.clock.J (m+2)) (A.clock.adm _) (upstairs A _ h)) n (A.S.block m).val
def spot (A:Levels G)(m)(Ñ:ChartRatio G)(h:5≤ A.clock.J (m+1))(p:cottage A m n h): Usage A Ñ m:=visits Ñ _ _ p
lemma growL (G:Gauge)(K: KernelChoices)(e j:ℕ): ∀ᶠ L:ℕ in atTop,∀ (A:Levels G)(m:ℕ),A.clock.kernel=K → A.clock.J (m+1)=j → (A.S.block m).val=L →∀ h:5≤ A.clock.J (m+1), cottage A m e h:=by
    have hv (i l): ∀ᶠ L:ℕ in atTop,∀ (A:Levels G)(m:ℕ),A.clock.kernel=K  →  A.clock.J m=i → A.clock.J (m+1)=j → A.clock.J (m+2)=l → (A.S.block m).val=L →∀ h:5≤A.clock.J (m+1), cottage A m e h:=by
       by_cases h:4≤ i ∧ 5≤ j ∧ 5≤l
       · obtain ⟨a,b,c⟩:=h; filter_upwards [Craft.demand (raySmall G K i j a b) (raySmall G K j l (by omega) c) e] with L he; intro A m x y z v u t; subst_vars; exact he
       apply Eventually.of_forall; intro _ A m i j k v e g; apply False.elim; apply h; subst_vars; exact ⟨A.clock.adm _, g, upstairs A _ g⟩
    let S:= Finset.range (j+2)
    filter_upwards [(eventually_all_finset S).mpr fun i _=> (eventually_all_finset S).mpr fun l _=> hv i l] with L hh
    intro A m x y t g; have he:= A.fits.stepSlow (m+1); have ht:= A.fits.mono m.le_succ; change A.clock.J m ≤ A.clock.J (m+1) at ht; change A.clock.J (m+2)≤ A.clock.J (m+1)+1 at he
    exact hh _ (show A.clock.J m∈ S from Finset.mem_range.mpr (by omega)) _ (show A.clock.J (m+2)∈ S from Finset.mem_range.mpr (by omega)) A m x rfl y rfl t g
private lemma inning {K K':KernelChoices}{u v:ℕ} (f:∀ (K:KernelChoices) (i j:ℕ),Tokenizer K G i j→ℝ) (a:K=K')(b:i=u)(c:j=v){e:4≤ i}{h:5≤ j}{e':4≤ u}{h':5≤ v}: f K i j (raySmall G K i j e h)= f K' u v (raySmall G K' u v e' h'):=by subst_vars; rfl
lemma equipping {A A':Levels G}{m m':ℕ}{Ñ:ChartRatio G}(h:A'.clock.kernel=A.clock.kernel)(t:A'.clock.J m'=A.clock.J m)(y:A'.clock.J (m'+1)=A.clock.J (m+1))(b:A'.clock.J (m'+2)= A.clock.J (m+2))(e:A'.S.block m'=A.S.block m) (p:5≤A.clock.J (m+1))(p':5≤A'.clock.J (m'+1))(q:cottage A m i p)(q':cottage A' m' i p') : (spot A m Ñ p q).gear=(spot A' m' Ñ p' q').gear:=by
    have hw: loose A m=loose A' m':= by
       have hh:(loose A' m').J=(loose A m).J:= y; have hv:(loose A' m').L=(loose A m).L:=e; cases g:(loose A m); cases g':(loose A' m'); simp_rw [g,g'] at hh hv; subst_vars; rfl
    unfold spot Usage.gear; congr 1
    all_goals try first | exact hw | exact h.symm
    case e_past=> exact inning (fun _ _ _ t=> t.outlet) h.symm y.symm b.symm
    case e_s=> exact inning (fun _ _ _ t=>t.s) h.symm t.symm y.symm
    case e_σ=> exact inning (fun _ _ _ t=>t.outlet) h.symm t.symm y.symm
    case e_preB=> exact inning (fun _ _ _ t=>t.preB) h.symm t.symm y.symm
    case e_sig=> exact inning (fun _ _ _ t=>t.sig) h.symm t.symm y.symm
    case e_D=> dsimp only [Bank.visits]; rw [hw]; exact inning (G:=G) (fun _ _ _ t=>t.bid (loose A' m')) h.symm t.symm y.symm

lemma growers (K:KernelChoices) (L: Side)(j e:ℕ)(Ñ:ChartRatio G) (d:Gear G→ℝ): ∀ᶠ c:ℝ in atTop,∀ (A:Levels G)(m:ℕ),A.clock.kernel=K  → A.clock.J (m+1)=j → A.S.block m=L→∀ (p:5≤ A.clock.J (m+1))(v:cottage A m e p), Escrow (spot A m Ñ p v) e c ∧ d (spot A m Ñ p v).gear ≤ c :=by
    have hx (i l) : ∀ᶠ c:ℝ in atTop,∀ (A:Levels G)(m:ℕ),A.clock.kernel=K → A.clock.J m=i → A.clock.J (m+1)=j → A.clock.J (m+2)=l → A.S.block m=L →∀ (p: 5≤A.clock.J (m+1))(q:cottage A m e p),Escrow (spot A m Ñ p q) e c ∧ d (spot A m Ñ p q).gear≤ c :=by
       by_cases h:∃ (A:Levels G)(m:ℕ),A.clock.kernel=K∧A.clock.J m=i∧A.clock.J (m+1)=j∧A.clock.J (m+2)=l∧A.S.block m=L ∧∃ p:5≤A.clock.J (m+1),cottage A m e p
       · obtain ⟨A,m,u,v,w,t,a,p,g⟩:=h; subst_vars
         filter_upwards [cooled Ñ _ _ g,eventually_ge_atTop (d (spot A m Ñ p g).gear)] with c hh hd
         intro A' m' h u v w t hp hg; have he:(spot A m Ñ p g).gear=(spot A' m' Ñ hp hg).gear:= equipping h u v w t p hp g hg; exact ⟨match_escrow he h u t hh, he ▸ hd⟩
       apply Eventually.of_forall; intro c A m u v w t e p q; exact False.elim (h ⟨A,m,u,v,w,t,e,p,q⟩)
    let S:= Finset.range (j+2)
    filter_upwards [(eventually_all_finset S).mpr fun i _=> (eventually_all_finset S).mpr fun l _=> hx i l] with L hh
    intro A m x y t g; have he:= A.fits.stepSlow (m+1); have ht:= A.fits.mono m.le_succ; change A.clock.J m ≤ A.clock.J (m+1) at ht; change A.clock.J (m+2)≤ A.clock.J (m+1)+1 at he
    exact hh _ (show A.clock.J m∈ S from Finset.mem_range.mpr (by omega)) _ (show A.clock.J (m+2)∈ S from Finset.mem_range.mpr (by omega)) A m x rfl y rfl t g

section
variable (p:Sheet G)(F' D':ℕ→ℕ){Y:Rolls p}{Ω:Protection Y}
abbrev preBoard := fun j=> (eventually_atTop.mp (growL G p.kernel (F' j) j)).choose
abbrev dyePost (K:KernelChoices)(L:Side)(j e:ℕ)(Ñ:ChartRatio G)(d:Gear G→ℝ) := Real.exp (Real.exp (eventually_atTop.mp (growers K L j e Ñ d)).choose)
abbrev coolTax (p':Sheet G)(Q:Rolls p')(Ñ:ChartRatio G)(d:ℕ→ Gear G→ℝ):= fun j=> dyePost p'.kernel (Q.L j) j (F' j) Ñ (d (F' j))
end

variable {p:Sheet G}{F' D':ℕ→ℕ}{Y:Rolls p}{Ω:Protection Y}{V:Delays Ω}{o:Bar V}{b':Supply.Wait o}{A:Levels G}{Ñ:ChartRatio G}
lemma Venice (pL:Paid b' A)(i:ℕ)(b: ∀ i'≥i, 5≤ A.clock.J (i'+1)∧ e≤ F' (A.clock.J (i'+1)))(d:ℕ→Gear G→ℝ)(z: preBoard p F'≤ p.floorL)(v: coolTax F' p Y Ñ d ≤ V.betaEntry) : Nonempty ({ I:Marks A Ñ e i (zz A) // ∀ j (h:i≤ j), d (F' (A.clock.J (j+1))) (I.mass j h).gear ≤ zz A j ∧ (I.mass j h).σ=crestM A j (b j h).1}):=by
    have ht j : A.S.block j=Y.L (A.clock.J (j+1)):=by rw [←A.fits.sameFactor,pL.lengths]
    have hu j (h:i≤ j): cottage A j (F' (A.clock.J (j+1))) (b j h).1:=by
        let k:= A.clock.J (j+1); have he: preBoard p F' k ≤ (A.S.block j).val:= le_trans (le_trans (z k) (Y.large k).need) (le_of_eq (congr_arg Subtype.val (ht j).symm)); exact (eventually_atTop.mp (growL G p.kernel (F' k) k)).choose_spec _ he A j pL.kernel rfl rfl (b j h).1
    let I j (h:i≤ j):= spot A j Ñ (b j h).1 (hu j h)
    have he j (h:i≤ j): Escrow (I j h) e (zz A j)∧ d (F' (A.clock.J (j+1))) (I j h).gear ≤ zz A j:=by
        let k:=A.clock.J (j+1); let U:= eventually_atTop.mp (growers p.kernel (Y.L k) k (F' k) Ñ (d (F' k))); let C':= U.choose
        have hQ : Real.exp (Real.exp C') ≤ A.clock.hatBeta j:=le_trans (v k) (pL.pays _)
        have hx : C'≤ zz A j:=by have h:=Real.log_le_log (Real.exp_pos _) hQ; rw [Real.log_exp] at h; have ht:=Real.log_le_log (Real.exp_pos _) h; rw [Real.log_exp] at ht; exact ht.trans (le_add_of_nonneg_left zero_le_one)
        obtain ⟨hv,f⟩:= U.choose_spec _ hx A j pL.kernel rfl (ht j) _ (hu j h); exact ⟨further hv (b j h).2 le_rfl, f⟩
    exact ⟨⟨⟨I,fun i p=>(he i p).1,fun _ _=> le_rfl⟩,fun j h=>⟨(he j h).2,rfl⟩⟩⟩
end YM.WilsonCoeffUV.Wheel.Cadenza
