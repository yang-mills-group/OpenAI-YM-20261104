import YM.MSbar.Mosaic.Cedar
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Mosaic
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz Ruby
open Next.SectorChange Bulk Posture JetTab
variable {G:Gauge}
namespace Issue
variable {ι:Type}{X f' g H0:ι→ℝ}{A:ι→Issue G}{φ:Filter ι}[φ.NeBot] (hX:Tendsto X φ atTop) (χ:ChartRatio G)(J:Voice G)(H H':Stage)(K:Patch)(D:KernelChoices)
variable (hG:G.Simple) (hD:K.Branches D G)(hQ: Clear G J)(hχ:LocalRatio χ)
local notation "α'" i=> tip G K.L (X i)
local notation "Y"=> fun i:ι=> tip G K.L (X i)
local notation "w'" i=> vol (tip G K.L (X i))
local notation "t'" i=> (A i).fClock
variable (hp:∀ᶠ i in φ,Paid (A i) K H H' J (X i)) (hq:∀ᶠ i in φ,(A i).S.kernel=D)
variable (W:(i:ι)→Positions (Primary (A i).c G))(hW:∀ᶠ i in φ,‖W i‖ ≤ hull (X i))
variable {p m k q L:ℕ}
variable (M:StageCost)(i':G.ColorIndex){s' e ν b:ℝ}(hc:∀ᶠ i in φ,Festival (A i) χ p i' ∧ ClockD (A i) p m M.s (X i)∧ Cs (A i) χ M.s p m (X i) i' (f' i) b ∧ Issue.Receipt (A i) M (X i))
variable (z:(i:ι)→Site (A i).f)
local notation "λ'" i=> Cane.value (αm i) M.C M.A M.E M.s M.sway
variable (hR:∀ᶠ i in φ,Ore M (X i) K) -- conduit.
variable (P:Palisade){τ b' :ℝ}(B :ℝ)
local notation "x'" i=> boxX (tip G K.L (X i)) (z i)
local notation "x₁" i=> boxY (tip G K.L (X i)) (z i)
local notation "N"=> k*(p+2)
local notation "N'" i=> Fintype.card (Lake (A i).F (boxX (α' i) (z i)) G)
local notation "N₁" i=> (keepB (A i).F (x' i) G).card
local notation "N₂" i=> (keepF (A i).F (x' i)).card
local notation "Γ" i=> crownP (A i).F (A i).M (W i)
local notation "Φ'" i=> inkW (N₂ i)
variable (h₁:p+2 ≤ m)(ha:Run φ X f' 0)(hk:k=m+1)(hT:p+3≤ k)(hμ:4 ≤ m)(hb:0<τ)(hb':0≤b')
variable (hK:∀ᶠ i in φ, Issue.Buy (A i) (W i) (boxX (tip G K.L (X i)) (z i)) (boxY (tip G K.L (X i)) (z i)) J P χ (tip G K.L (X i)) e s' (thorn (tip G K.L (X i)) (k*(p+2))) τ b')
include hX hp hc hR hW hχ hG hQ h₁ ha hk hT hμ hb hb' hq hK
-- choose all arrays independent of U inside. true film.Tribe bound.Emark.P.States. includes luminosity `E` meas.
variable (hB: 0≤ B)(hT₁: Run φ (fun i=> tip G K.L (X i)) H0 0)(he1:∀ᶠ i in φ,0 ≤ H0 i)
include hB hT₁ he1
local notation "V'" i=> ((A i).S.patch.L.val*closeN (Y i))
local notation "Y'"=> Y
omit hp hc hR hW hχ hG hQ h₁ ha hk hT hμ hb hb' hq hK hB hT₁ he1
lemma costZ(τ:ℝ)(hb:0<τ)(p:ℕ):
      Van φ X (fun i=> 2*Real.exp (-(Real.log (X i)/τ*Real.log (X i))+ τ*(Real.log (X i)/τ)^2/2)) :=by
    let v:= (τ*2)⁻¹; have hv:0<v:=by unfold v; positivity
    have he(z:ℝ) : -(z/τ*z)+τ*(z/τ)^2/2= (-v)*z^2:=by unfold v; field_simp; ring
    simp_rw [he]; intro a; exact Run.mulK hX (Van.castE hX (neg_lt_zero.mpr hv) a) 2
include hp hc hR hW hχ hG hQ h₁ ha hk hT hμ hb hb' hq hK hB hT₁ he1
set_option maxHeartbeats 850000 in
lemma portion : ∃ (O:ι→Ages)(W':ι→Salary)(E E':ι→ℝ), Run φ Y (fun i=>(O i).outer) 0 ∧ Run φ Y (fun i=> Salary.stamp (W' i) p (N' i) (t' i) (E i) (E' i)) (epsW p)∧ ∀ᶠ i in φ,Issue.Projection (A i) χ P J (O i) (W' i) (W i) p k (z i) (tip G K.L (X i)) (H0 i) B (E i) (E' i) b':=by
     let n:=fun i=> N' i; let x:=Y; let v(i):= vol (x i); let r(i):=(A i).fClock; let b1(i):= N₁ i; let b2(i):= N₂ i; let a(i):= αm (x i); let q(i):= (A i).S.patch.L.val*closeN (x i)
     obtain ⟨c1,c2,c3,c4,k1,k2,C,U,V,ψ,hΨ,hU,hV,hc1,he⟩:=stockS hX χ J H H' K D hG hQ hχ hp hq W hW M i' hc z hR P h₁ ha hk hT hμ hb hb' hK -- order
     let HT (i):=5*goalP (x i) p -- shadow
     let O(i):= Ages' c1 c2 c3 c4 (U i) (V i) C (ψ i) k1 k2 (HT i) (v i)
     let sP(i):=O i|>.cost (r i) p G ((A i).S.patch) (b1 i) (b2 i)
     let p'(i):=Bmark G N 0 p k (q i) (z i) B (O i).outer (a i); let C'(i):=barry 0 N p ((liftW (a i) 0 (q i))*B) (O i).outer; let e'(l:ℕ)(i):=Emark (O i) (p' i) (C' i) (r i) k l p; let Y₁(i):=e' k i
     obtain ⟨h1,h2,h3⟩:= facing hX K z; have hk':(fun i=> (O i).outer)= V:=rfl
     have hv:Tendsto x φ atTop:= (Work.E09.betaF_growth G K.L).comp hX; let E:=fun p g=> Run φ x g p; obtain ⟨hr,hc'⟩:= roundS hX J H H' K hG hp -- shadow fix
     have hx:Run φ x HT (pawn p):= Run.mulK hv (Run.core hv _) _; have hw':Run φ x v 0:=(Run.stanza hv).mulY hv _
     have hs: Run φ x sP (epsW p):=(Run.tariff hv K G c1 c2 c3 c4 k1 k2 C hr hU hV hx hw' hΨ h2 h1).alter (hp.mono (fun i he=> (by unfold sP; rw [he.space]))) -- implicit
     have hz :Run φ x (fun i=> liftW (a i) 0 (q i)) 0:=by
           have ht:=nearB hv 1 one_pos 0 K.L.val|>.2; simp_rw [one_mul] at ht; apply Run.alter ht; filter_upwards [hp] with i hi; unfold q; rw [hi.space]; -- rfl
     have hC:Run φ x C' 0:=by unfold C' barry; exact Run.mulK hv ((hz.mulY hv B).Ymul hv ((Run.addR hv (Run.token hv _) hV).Ypow hv _)) _
     have ht':Run φ x p' 0:=by
           let A'(i):=plateD (z i) (a i) p 0 N k (q i) B
           have hP :Run φ x A' 0:=(Run.token hv _).addR hv ((((hz.mulY hv B).mulK hv _).mulK hv _).mulK hv _)
           unfold p' Bmark barry; exact Run.mulK hv ((hP.Ypow hv _).Ymul hv ((Run.addR hv (Run.token hv _) hV).Ypow hv _)) _
     have he' :Run φ x Y₁ (epsW p) := by
           let F(i):= spoolP (p' i) (C' i) (k1*(V i)^(p+3)) k; have h: Run φ x F 0:= by unfold F spoolP; exact (Run.token hv _).addR hv ((Run.Ymul hv (Run.addR hv ht' (Run.token hv _)) (Run.addR hv (Run.mulK hv (hV.Ypow hv _) k1) hC)).mulK hv _)
           exact Run.Yrat hv (Run.tr hv hr) (Run.Ypow hv h _)
     let Q(i):=pillow (x i); let F(i):= room (x i); let D' :=fun i=> topP J P (x i); let v'(i):=(D' i+F i+b'*(D' i+Q i))/ r i; let t(i):= loftM p N (b1 i) (H0 i) (V i); let ψ'(i):=Real.log (x i); let γ(i):= storm (n i) (ψ' i/τ) (ψ' i) τ; let ξ(i):=(x i)^epsW p; let w(i):= gear (N+2) τ (t i) (p' i) (inkW (b2 i) G (O i).w (O i).U) (v' i) (ξ i) (γ i);
     let Δ:= fun i=> (w i|>.payΔ);
     have hf:Run φ x t 0:= by unfold t loftM; exact Run.mulK hv ((hT₁.Ymul hv ((Run.addR hv (Run.token hv _) hV).Ypow hv _)).Ymul hv h2) _
     have hχ':Run φ x Δ (pawn p):=by unfold Δ w gear inkW; dsimp only [O,Ages']; push_cast; exact hx.Yrat hv ((Run.mulY hv h1 ↑G.lieDim).Ymul hv (hw'.mulK hv _))
     have hy:Run φ x v' 0:=by
           obtain ⟨h1,h2,h3,h4,h5⟩:= height hv P J; let hD':= h5.loosen (show (-1:ℝ)≤ -(1/2) by norm_num); exact (Run.mulR hv (Run.addR hv (Run.addR hv hD' h2) ((Run.addR hv hD' h3).mulK hv _)) hc'.1).loosen (by norm_num)
     have hU:Run φ x (fun i=> (w i).payP) 0:= Run.Ymul hv hf ((Run.addR hv (Run.token hv _) hy).Ypow hv _)
     have hF:Run φ x (fun i=> (w i).payT) 0:= Run.Ymul hv ht' ((Run.addR hv (Run.token hv _) hy).Ypow hv _)
     have hζ:Run φ x (fun i=>(ξ i)⁻¹) (-(epsW p)):=by apply (Run.core hv _).alter; filter_upwards [hv.eventually_ge_atTop 0] with i hi; unfold ξ; rw [Real.rpow_neg hi]
     have hγ:Van φ x γ:=by let f(i):=2*Real.exp (-(ψ' i/τ*ψ' i)+τ*(ψ' i/τ)^2/2); have hh:Van φ x f:=costZ hv τ hb 0; unfold γ storm; simp_rw [mul_comm ((n _:ℕ):ℝ)]; exact Van.mulL hv h3 hh -- binder simp issue `_`
     have hξ:Run φ x ξ (epsW p):= Run.core hv _
     have hQ:Run φ x (fun i=>(w i).nameP (sP i) p (n i) (r i)) (epsW p):=Run.primary hv hr hs hχ' h3 hξ hζ hγ hf hU (N+2) τ 1
     refine ⟨O,w,sP,Y₁,hV,?_,?_⟩
     · exact Run.stamped hv hr hs he' hχ' h3 hξ hζ hγ hf ht' hU hF (N+2) 1 τ
     let a':=-(1/2:ℝ); have hi: Tendsto (fun i=> r i*cloudK (n i) p (N+2) τ (t i)+ Δ i+(w i).nameP (sP i) p (n i) (r i)) φ (𝓝 0):=by
          have hh':pawn p<0:=(mp0 p|>.2.2).trans_lt (by norm_num); have hT: Tendsto (fun i=>r i*cloudK (n i) p (N+2) τ (t i)) φ (𝓝 0):= ((hr.Yrat hv (Run.spanP hv h3 p _ τ hf)).bouquet hv (by norm_num)); simpa using! ((hT.add (hχ'.bouquet hv hh')).add (hQ.bouquet hv (lt_trans (mp0 p|>.2.1) hh')))
     filter_upwards [he,hp,hK,hv.eventually_gt_atTop 1,(hr.Yrat hv hU|>.bouquet hv (by norm_num)).eventually (ge_mem_nhds zero_lt_one),hi.eventually (ge_mem_nhds (show (0:ℝ)<1/2 by norm_num)), tails hX J H H' K hG hp] with i He hP hK hv0 ht' hv' Hh -- Hi conflict
     have ht'':1 ≤ x i:=hv0.le; let X₀:= boxX (x i) (z i); let Xp:=(A i); have hg:0< cue (x i):=by unfold cue; positivity
     have hr:0<r i:= (half_pos hg).trans_le Hh.1.1
     have H':Temper (A i) J P χ (O i) p k (X i) (x i) (W i) (z i):=He
     let F:= Xp.F; let Hmat:=mold Xp.pre F Xp.v -- syntax
     let Λ:= includeX (G:=G) F X₀; let v₀ :=hK.fast
     have hΓ(i':Lake F X₀ G) : ((pinch Λ Hmat)⁻¹) i' i' ≤ τ:=by
            have hV : 0≤ thorn (x i) N :=by unfold thorn αm; exact div_nonneg (zpow_nonneg (sq_nonneg _) _) (Nat.cast_nonneg _)
            let K': Matrix (Lake F X₀ G) (Lake F X₀ G) ℝ:= (pinch Λ Hmat)⁻¹; let h:= embeds Λ (secureY F X₀ G) K'; have hp := v₀.sealed.single (by linarith only [hV] : (0:ℝ)+thorn (x i) N ≥0) (Λ i') (Λ i')
            apply le_trans (le_abs_self _); exact le_trans (le_of_eq (congr_arg abs ((congr_fun (congr_fun h i') i').symm))) hp
     refine ⟨H'.dollars,H'.origin,H'.upper,H'.check_,⟨H'.fees,H'.march,le_rfl,hΓ,?_,?_,le_rfl,le_rfl,le_rfl,?_,ht',le_rfl,hv'⟩,?_⟩
     · have hp:0≤ ψ' i:= Real.log_nonneg ht''; refine ⟨ψ' i,ψ' i/τ,?_,hp,div_nonneg hp hb.le,le_rfl⟩; apply le_trans (mul_le_mul_of_nonneg_left Hh.1.2 hp); unfold pillow distance; change ψ' i*(2*cue ..)≤ 3*(x i ^(-(1/2:ℝ))*Real.log (x i)); rw [Real.rpow_neg (zero_le_one.trans ht''), ←Real.sqrt_eq_rpow]; change ψ' i * (2*cue (x i)) ≤ 3*(cue (x i)*ψ' i); linarith only [mul_nonneg hg.le hp]
     · exact Real.rpow_pos_of_pos (zero_lt_one.trans_le ht'') _
     · refine ⟨v' i, ?_,le_rfl,le_rfl⟩; change _≤ r i*v' i; unfold v';  rw [mul_comm (r i),div_mul_cancel₀ _ hr.ne']
     intro l hl s0; let S:=spoolP (p' i) (C' i) ((O i).k1*(O i).outer^(p+3)) k; have hv1:1 ≤ (O i).outer:= H'.dollars; have hk1:0 ≤ (O i).k1:=hc1; have hE :0 ≤ liftW (a i) 0 (q i):=(wpos ..).le
     have ht:0 ≤ p' i:=by unfold p' Bmark plateD barry; positivity
     have he0:0≤ C' i:=by unfold C' barry; positivity
     have hA:1≤ S:=by unfold S spoolP; change 1 ≤ 1+2^k*((p' i+1)*((O i).k1*(O i).outer^(p+3)+C' i)); apply le_add_of_nonneg_right; positivity
     change r i ^(p+1)* S^l ≤ r i^(p+1)* S^k; gcongr
end Issue
end YM.MSbar.Mosaic
