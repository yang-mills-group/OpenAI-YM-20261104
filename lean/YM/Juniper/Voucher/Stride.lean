import YM.Juniper.OrbitPrice.Carry
import YM.Juniper.Voucher.Wing
/- narrow real stance (no perm choices) -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Voucher
open UVExtension UVExtension.Tabernacle RG Shoot Wilson Lattice Pressure Dales PhysicalNext Input AnalyticBridge VerifiedReset Ovens Progress.DirectedRecipe Oriel Oriel.Charted
open Push Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge} {d:Levels G}{i n:ℕ}{T:Cham d i n}(a b : Valve i n d T)
local notation "P"=> d.budget i
local notation "E"=> d.clock.allowance i
local notation "K"=> d.clock.forcedAllowance i
local notation "L"=> Dales.place d i n T
variable {η y z ε p q:ℝ}{t u:Tabernacle.Field G (d.S.side i n)}
variable (hp:a.val=t)(ht:b.val=u) (hk:t.2=u.2)
include hp ht hk
lemma delta_bill (he:(floor P (t-u)).EBound P η)(hb:0 ≤ y)(h:η≤ y* E): ‖L a - L b‖ ≤ y:= by
    have hq:a.val.2=b.val.2:= by rw [hp,ht,hk];
    have hZ: Native.trueK a = Native.trueK b:= by exact (congr_arg (fun x=>(K)⁻¹ • (vibe (ChimeK G P (d.S.side i n)) x) : (ℕ → Config G (d.S.side i n) → ℝ)→_) hq)
    rw [Native.total_split,hZ,sub_self,norm_zero]; exact max_le ((Native.standard_le_emission a b _ hb).2 (by rw [Submodule.coe_sub,hp,ht]; exact Time.E_rises he h)) hb
-- stride val
omit hp
lemma room_b (h:(floor P u).Valid P p q)(hv:(floor P t).KBound P z)(hz:z ≤ η*K)(hh:p ≤ η*E): ‖L b‖ ≤ η:= by
    apply (Native.pay_total b _).2; rw [ht]; obtain ⟨w,hw,hW⟩:= Time.K_rises hv hz
    refine {h with boundE:=Time.E_rises h.boundE hh,boundK:=⟨w,?_ ,hW⟩}; change ∀ i,0≤w i ∧ ∀ V,‖u.2 i V‖≤ w i; rw [← hk]; exact hw
end YM.Juniper.Voucher
