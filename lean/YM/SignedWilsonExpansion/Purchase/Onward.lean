import YM.SignedWilsonExpansion.Purchase.Shoot
import YM.SignedWilsonExpansion.Purchase.BlockedTrial
import YM.FullVolume.Cross
/-! # physical receipts oil panel
This part takes ONE actual original Run and derives its enrollment costs. Optical election supplies extra path O names later, no independence replacement here.
-/
set_option autoImplicit false
set_option maxHeartbeats 880000
noncomputable section
namespace YM.SignedWilsonExpansion.Purchases
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Quince Quince.PreCost
open Asymptotics WilsonCoeffUV.Bank Function Filter Matrix Lattice RG Wilson Gauge Extra.Histories Analysis
open WilsonCoeffUV.Mer.Xa.FetchP Labels Trace.Physical.Germ Trace.Physical.GermGraph
open Source Work.G08 Next.Rank.Price Next.Rank Perch MergeProof Commission Real BlockedTrialVoice
open scoped Classical ContDiff BigOperators Topology
variable {G:Gauge}{d j m N p n i:ℕ}
local notation "Rm!" => Run
variable (R: Rm! G)
local notation "C"=> R.family
set_option quotPrecheck false
local notation "H"=> R.family.path
local notation "T"=> (H).levels
local notation "F"=> (C).labels.level d
local notation "W"=> (C).localSection d
lemma care (g:G.Simple)(h:(C).ref d≤j)(v:j+n≤N)(x: Voice F H p (j+n))(hx: Heard W H N p (C).params (j+n) x)(ht: Chorus H N p (j+n) x):∃ X:∀ k:ℕ, Voice F H p k,X (j+n)=x ∧ lives C d N p j n X ∧
    ∀ i∈ Finset.Ico j (j+n), ∀ a:C|>.label d, ((X i).plays a).density 0 W ((H).rep N p i)= blast H N p i d (((X (i+1)).plays a).density 0 W ((H).rep N p (i+1))):=by
    induction n with
    | zero=> let X(i:ℕ):= BlockedTrialVoice.trial F H N p i; let Y:=update X j x; exact ⟨Y,update_self ..,fun i hi=>by simp only [Nat.add_zero, Finset.Icc_self,Finset.mem_singleton] at hi; subst i; rw [show Y j = x from update_self ..]; exact hx,fun i hi=> by simp at hi⟩
    | succ n ih=>
       have age:j+n<N:=by omega
       obtain ⟨door,_,fund⟩:=Bandage.chorus g R.b R.T R.tuning.receipts N p (j+n) age
       obtain ⟨⟨tags,finite,keeper,owns,S,a,c,stamp,buy⟩,honest,toll,hard⟩:= fund d ((R.accepts d).trans (R.alloy.B.a.fits.mono (show R.t d ≤ j+n from h.trans (Nat.le_add_right ..))))
       obtain ⟨U,hu,reports,uc,_⟩:=repriseQ W H N p (C).params R.w (j+n) x R.makes.wilson age hx R.b.clock.room R.b.clock.bank S door honest tags toll stamp finite hard buy keeper owns ht (R.makes.sections d) (fun X=>(Tour.bright H R.makes.wilson N p _ age X).ne')
       obtain ⟨X,c,hX,hZ⟩:=ih age.le U hu uc; let Y:=update X (j+(n+1)) x; have hp0:Y (j+(n+1))=x:=update_self ..; have h'(k)(t:k≤j+n):Y k=X k:= update_of_ne (by omega) ..; let hk:Y (j+n)=U:= (h' _ le_rfl).trans c; refine ⟨Y,hp0,fun i hi=>?_,fun i hi v=>?_⟩
       · rcases eq_or_ne i (j+(n+1)) with hp|hp; · subst i; rwa [hp0]
         obtain ⟨hy,hk⟩:= Finset.mem_Icc.mp hi; have ht:i≤j+n:=by omega
         rw [h' i ht]; exact hX i (Finset.mem_Icc.mpr ⟨hy,ht⟩)
       obtain ⟨hy,hk'⟩:=Finset.mem_Ico.mp hi
       by_cases he:i=j+n
       · subst i; rw [hk, show Y (j+n+1)=x from hp0]; exact reports.values v
       have hv:i<j+n:=by omega
       rw [h' _ hv.le,h' _ hv]; exact hZ i (Finset.mem_Ico.mpr ⟨hy,hv⟩) v
lemma issueQ (g:G.Simple)(h:(C).ref d≤j)(v:j+n≤N)(p:ℕ): Nonempty (PurchVoice R.family d N p j n):=by
    let V:= BlockedTrialVoice.trial F H N p (j+n); have hc:Chorus H N p (j+n) V:=by
       constructor; intro x s; funext X U; simp [V,BlockedTrialVoice.trial,primary,floatUp,stepUp,profile,cram,Motion.scalar]
    obtain ⟨X,p,f,hQ⟩:=care R g h v V (BlockedTrialVoice.enrolled R.makes.wilson (R.makes.sections d) v) hc; refine ⟨X,f,hQ,fun a=>?_⟩ ; rw [p]; rfl
lemma spinsC (hs:(C).ref d≤j)(h:j≤N) : Spinning C d j N p:=by
    intro s x; let c:=(C).factory d N p; let z:=c.terminal; let P(v):= Extra.Histories.Motion.patch F s v; have p0:(C).ref d≤N:= hs.trans h; obtain ⟨m,a,f,u,w⟩:=R.books _ N p p0; have he:=u.earned j hs h
    have h0: z (P (z.symm x))=P x:=by
        let H':= (R.makes).calibrated d N p p0; let H₀:= H'.orients s.1 (z.symm x); change z ((F).act s.1.ortho (z.symm x))=(F).act s.1.ortho (z (z.symm x)) at H₀; rw [ LinearEquiv.apply_symm_apply ] at H₀
        unfold P Extra.Histories.Motion.patch; split; · exact ( H'.realForm _).trans (congr_arg star H₀)
        exact H₀
    have hx(v):columns C d j N p v=(m.tone j).index (z.symm v):= by change ((R.stories d N p).entries j (z.symm v)).x= _; erw [f]; exact he.currents _
    erw [hx,hx]; change (m.tone j).index (z.symm (P x))=P ((m.tone j).index (z.symm x)); erw [show z.symm (P x)= P (z.symm x) from z.injective ((LinearEquiv.apply_symm_apply ..).trans h0.symm)]; exact (he.moves ..).symm
open SignedWilsonExpansion.Purchases UVClock PurchVoice
abbrev clockLine (A:Levels G)(j k:ℕ)(Y:ℝ): Prop:=∀ i∈ Finset.Ico j (j+k), ((A.S.block i).val:ℝ) ≤ Y
abbrev ζFront (A:Levels G)(Y:ℝ)(j:ℕ):ℝ:= (2+Y)*(Real.sqrt (A.clock.monitor j))⁻¹
abbrev SmallEnough (A:Levels G)(j:ℕ): Prop:=∀ i≥j,A.clock.threshold (i+1)≤A.clock.threshold i ∧ cameo A i≤ cameo A (i+1)
lemma birthQ (A:Levels G)(g:G.Simple): ∀ᶠ i:ℕ in atTop, SmallEnough A i:=by
    have ht: ∀ᶠ i:ℕ in atTop, cameo A i≤ cameo A (i+1) := by
        let B(i):= A.clock.hatBeta i; filter_upwards [ (Real.tendsto_log_atTop.comp ( hat_rateM A g )).eventually_ge_atTop 1] with i hi; apply Real.sqrt_le_sqrt; apply Real.exp_le_exp.mpr; refine pow_le_pow_left₀ (Real.log_nonneg hi) (Real.log_le_log (zero_lt_one.trans_le hi) (Real.log_le_log (zero_lt_one.trans (A.fits.delayed i)) (hat_monoM A g i.le_succ))) _
    obtain ⟨K,h⟩:= eventually_atTop.mp (ht.and ( threshold_decr A g )); filter_upwards [eventually_ge_atTop K] with i hi; exact fun p hp=> ⟨( (h p (hi.trans hp) ).2 (p+1) p.le_succ),(h p (hi.trans hp)).1⟩
variable (SootQ:Skill R.b (bear R.w))
lemma Step_quote (S:Skill R.b (bear R.w))(g:G.Simple){Y:ℝ}(hy:1≤Y)(s:(n:ℝ)≤Y)(h:(C).ref d≤j)(p:SmallEnough T j)(hV:clockLine T j n Y)
    (Tt: (recoverDose F).buy Y*(ζFront T Y j)≤1/2):
    ∀ᶠ p':ℕ in atTop,∀ N:ℕ,j+n≤N→∃ Q:ℕ→ ((C).label d→ₗ[ℂ](C).label d),FrontStep C d j n N p' Y (ζFront T Y j) Q:=by
    let Z:( ℕ→ℝ):= (fun i=>cameo T i); have h0:0≤2+Y:=by linarith
    let χ:= ζFront T Y j; have hz(i):0<Z i:= cameo_pos ..; have hx:0≤χ:= mul_nonneg h0 (inv_nonneg.mpr (hz j).le)
    let I:=Finset.Ico j (j+n); have hw(a:ℕ)(hp:j ≤ a) : Z j ≤ Z a:=by induction a,hp using Nat.le_induction with| base=>exact le_rfl|succ i v ih=> exact ih.trans (p i v|>.2)
    have he(i:ℕ)(hp:i∈I):
       ∀ᶠ u:ℕ in atTop,∀ N:ℕ,j+n≤N→∃ t:(C).label d→ₗ[ℂ] (C).label d,CapsuleAt (T).clock.threshold F H (C).params W i N u (Y^(d+1)) χ t:=by
         obtain ⟨a,v⟩:=Finset.mem_Ico.mp hp; have he:=(hV i hp); filter_upwards [job R.b R.T R.tuning.receipts g S ( ( R.accepts d ).trans (R.alloy.B.a.fits.mono (h.trans a)) ) (hV i hp) (p i a |>.1)] with u hi N ht
         obtain ⟨U,f⟩:= hi N (v.trans_le ht); refine ⟨U,f.carries,f.tunes,fun A X x y z t=>?_⟩
         exact (f.price A X x y z t).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (inv_anti₀ (hz j) (hw (i+1) (by omega))) h0) (add_nonneg (size_nonneg ..) (size_nonneg ..)))
    filter_upwards [(Finset.eventually_all I).mpr he] with p hp N he; choose U hU using fun i: (↑I : Type) => hp i i.2 N he; let T'(k): (C).label d→ₗ[ℂ] (C).label d:= if v:k∈I then U ⟨k,v⟩ else 0; refine ⟨T',fun i v=> ?_,hy,hx,Tt,s⟩; rw [show T' i= U ⟨i,v⟩ from dif_pos v]; exact hU ⟨i,v⟩
lemma elect_lead (A: Levels G) (d:ℕ)(G':G.Simple)(F':Frames G){ι:Type}{L:Filter ι}{B Y:ι→ℝ} (h:Rise B L)(p:CashY L B (1:ι→ℝ) Y){j:ι→ℕ}(z:Epoch L B A j) : CashY L B ( cent B ) (fun i=> ζFront A (Y i) (j i)) ∧ Tendsto (fun i=> (recoverDose ( F'.level d )).buy (Y i)*ζFront A (Y i) (j i)) L (𝓝 0):=by
    have hv:CashY L B (cent B) (fun i=> ζFront A (Y i) (j i)):=by
       simp only [ζFront, ss_nifty]; simpa only [one_mul,CashY] using! Wage.mul (Wage.plus (spreadMax h) (Wage.unitC (2:ℝ) ) p) (markS h z (-1/2))
    exact ⟨hv,Wage.next_zero (Wage.mul ( Wage.ornament _ _ p ) hv ) ( by simpa only[one_mul] using! daybreak h )⟩ -- defeq second p money
-- payable period thresholds `Step_quote`, then period filter after visit.L.Price.P full quoting; use elected path.Depth.D marker.Cost scheduling `ticket_length`.
end YM.SignedWilsonExpansion.Purchases
