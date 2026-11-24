import YM.MSbar.Pole.Sew.Base
/-!
# Insert a kinetic shape at scale `s` before a dimensional loop operation

`Skin` is a pole germ on functions of both the screen and external arguments.
Use this budget before any momentum integration. No compact restriction in the
real wave variables and no smaller radius selected for some angle. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Set Function Filter MeasureTheory Ambient Age Momentum Mellin Symbol Sew Tip
open scoped Topology ContDiff BigOperators InnerProductSpace Classical
variable {I : Type} [Fintype I] {n : ℕ}

def Skin (k:ℕ) (F : ℂ→ Screened I) := ∃ (R:ℝ) (G : ℂ→ Screened I),0<R∧Sweep (zone R) G ∧ ∀ z∈slit R, ∀ n x,z^k*F z n x=G z n x

variable {k : ℕ}
namespace Sew
structure Thread (I : Type) where
  output : Finset I
  root : I
  left : I
  right : I
  chain : Chain I
  scalar : ℂ
namespace Thread
variable (T : Thread I)

def warp (n : ℕ) := bar T.output T.root T.left T.right n
lemma warps (x:External I n)(p:place n): T.warp n (p,x)=fill T.output T.root T.left T.right x p:=barred ..
def pre (r : ℝ) (G : ℂ → Cloud I) (z:ℂ): Screened I := fun n x=> Heat.wave r x.1 * T.scalar*G z n (T.warp n x)

def spun (r : ℝ)(F : ℂ→Cloud I) := T.pre r (fun z=> Chain.term T.left (dimension z) (F z) T.chain)

private lemma sphere {S:ℝ} (r : ℝ) (hr:0<r) {G:ℂ→Cloud I} (h : Meridian (zone S) G) : Sweep (zone S) (T.pre r G) := by
  constructor
  · intro n; let p := ticket (@Prod.snd (place n) (External I n)); let q := ticket (@Prod.fst (place n) (External I n))
    let L:= ContinuousLinearMap.fst ℝ (place n) (External I n)
    have hl : Wall (zone S) p q (fun _ x => Heat.wave r x.1) := by
      have ht:= Heat.cost (n:=n) hr
      refine (Wall.freeze ht).pull L (r:=p) (Bills.const _) (s:=q) ?_
      exact Bills.self
    have ht := hl.mul (show Wall (zone S) p 1 (fun _ _=> T.scalar) from ⟨Packet.const _,fun _ _ _=> differentiableAt_const _⟩)
    let v := T.warp n
    have hg : Wall (zone S) (p*q) 1 (fun z x=> G z n (v x)):= by
      refine (h.budget n).pull v (r:=p*q) ?_ (Bills.const _)
      refine bill_single (C:=1+‖v‖) (l:=1) (by positivity) fun x hx=> ?_
      have hh : 1+‖x‖ ≤ (p*q) x:= by rw [mul_price,mul_comm (p.val x) (q.val x)]; exact ticket_product x
      refine le_trans ?_ (show (1+‖v‖)*(1+‖x‖) ≤ _ by rw [pow_one]; exact mul_le_mul_of_nonneg_left hh (by positivity))
      change ‖1+‖v x‖‖ ≤ _
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith [v.le_opNorm x,norm_nonneg x,norm_nonneg v]
    exact ht.pays hg
  intro z hz
  constructor
  · intro n J p x; unfold pre; rw [T.warps,T.warps,Tip.turns,(h.tensor z hz).moves]; change Heat.wave r _*_*_=Heat.wave r _*_*_; rw [(show Heat.wave r (J p)=Heat.wave r p from (Heat.coherent I r).moves n J p x)]
  intro n v x; unfold pre; rw [T.warps,T.warps,Tip.pads,(h.tensor z hz).agrees]; change Heat.wave r _*_*_=Heat.wave r _*_*_; rw [show Heat.wave r (place.pad n v) = Heat.wave r v from (Heat.coherent I r).agrees n v x]

lemma collect {U V : Finset I} {F:ℂ→ Cloud I} (hs:Vortex k F) (r:ℝ)(hr:0<r)(hk:Acts U V F) (h : T.chain.usable) (hx:T.chain.reads ⊆ V) : Skin k (T.spun r F) := by
  obtain ⟨R,G,hR,H,he⟩:=Chain.whirl hs h T.left hx hk
  refine ⟨R,T.pre r G,hR,T.sphere r hr H,fun z hz n x=> ?_⟩
  unfold spun pre; rw [mul_left_comm,he z hz]
end Thread
end Sew
namespace Skin
lemma chart {F:ℂ→ Screened I}(h: Skin k F) : ∀ᶠ z in approaching, Sweep (Metric.ball 0 (1:ℝ)) (fun _=> F z) := by
  obtain ⟨R,G,hr,H,h⟩:=h
  filter_upwards [neighborhood hr] with z hz
  have hh : F z= (z^k)⁻¹ • G z:= by
    funext n x; change F z n x= (z^k)⁻¹* G z n x; rw [← h z hz,inv_mul_cancel_left₀ (pow_ne_zero k (show z≠0 from hz.2))]
  rw [hh]; constructor
  · intro n
    let K:= (H.budget n).fixed hz.1
    refine Wall.freeze ?_
    convert! K.mul (Packet.const ((z^k)⁻¹)) using 1; funext; exact mul_comm ..
  intro _ _; have he:=H.texture z hz.1
  exact ⟨fun n i a x=> congr_arg (((z^k)⁻¹)*·) (he.moves ..),fun i a n=>congr_arg (((z^k)⁻¹)*·) (he.agrees ..)⟩
lemma statuses {F:ℂ→ Screened I}(h:Skin k F) : ∀ᶠ z in approaching, Texture (F z) ∧ Breezes (F z) := (chart h).mono fun _ hz=>⟨hz.texture 0 (zone_zero zero_lt_one),hz.breeze (zone_zero zero_lt_one)⟩
lemma operate {F:ℂ→Screened I} (h : Skin k F) (μ:ℝ) (hμ:0<μ): Vortex k (Integrates μ F):=by
  obtain ⟨R,G,hr,H,h⟩:=h
  refine ⟨R,_,hr,integrates R (fun z hz=>((zone_mem ..).mp hz).le) Metric.isOpen_ball H μ hμ,fun z hz n x=> ?_⟩
  -- get F texture at this z via same hh
  have he : F z=(z^k)⁻¹ • G z:= ?_
  have hb:=H.breeze hz.1; have hp:=H.texture z hz.1
  have hc : Texture (F z):= by rw [he]; exact ⟨fun i a p x=> congr_arg (((z^k)⁻¹)*·) (hp.moves i a p x),fun i p x=> congr_arg (((z^k)⁻¹)*·) (hp.agrees i p x)⟩
  have hF : Breezes (F z) := ?_
  unfold Integrates; rw [Ambient.nat_scale hF hc hb hp x ((z^k)⁻¹) (dimension z) (by rw [he]; intro _ _; rfl)]; have hk:z≠0:=hz.2; rw [mul_assoc ((z^k)⁻¹),mul_inv_cancel_left₀ (pow_ne_zero k hk)]
  · rw [he]; intro i; convert! (hb i).mul (Packet.const ( (z^k)⁻¹)) using 1; funext; exact mul_comm ..
  funext n x; change _= (z^k)⁻¹ * G z n x; rw [← h z hz, inv_mul_cancel_left₀ (pow_ne_zero k (show z≠0 from hz.2))]
end Skin
end YM.MSbar.Pole
