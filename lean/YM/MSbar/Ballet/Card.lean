import YM.MSbar.Ballet.Gift
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Ballet
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Alto Mosaic Mosaic.Issue
variable {G:Gauge}
open Heath Stock -- Hunger Horizon conflict. 
variable (O:ChartRatio G)(K:MapPrices)(p s m:ℕ)(j i:ℕ)(H H':Stage)(P:Patch)(X:KernelChoices)(B:Uniform.Before G H'.width H'.paths j X (p+3)) (u:G.ColorIndex)(W:Voice G)
noncomputable def QCost (O:ChartRatio G)(K:MapPrices)(p s j i:ℕ)(H':Stage)(P:Patch)(X:KernelChoices)(B:Uniform.Before G H'.width H'.paths j X (p+3)):Fees:= let a:=Parma.grain H'.clip P B (K.α j);tango K j i s p P O B a (B.tables H'.clip P)
local notation "Q!"=> QCost O K p s j i H' P X B
structure Sent (x:ℝ): Prop where
  aim: Asked K O H' j i X P s p x B
  world: ∀ (A:Mosaic.Issue G),Issue.Paid A P H H' W x→A.S.kernel=X→ Festival A O p u→ClockD A p m s x→Cs A O s p m x u (purse Dean (hatW x) p) (bigF (seats K j i s))→Issue.Receipt A (stamping (QCost O K p s j i H' P X B) s) x→ m+1 ≤ A.post.p.order→hatW (tip G P.L x)^4 ≤ A.f.val→hatW x^4 ≤ A.c.val→ Geneva.Gain A O p m s x
variable (h:G.Simple)(hχ:LocalRatio O) (hp:Prepared K j P.L G)(hS:6 ≤ s)(hZ:m ≤ j)(hr:p+2 ≤ m)(hm:4 ≤ m)(hv:s ≤ j)(he:i ≤ j)(hk:P.Branches X G)(hz:P.J=j)(hU:Clear G W)
include h hχ hp hS hZ hm hv he hk hU hr hz
lemma card : ∀ᶠ x:ℝ in atTop,Sent O K p s m j i H H' P X B u W x:=by
   have ht:= need O p s j i H' P K h (hp.pre.1 _ _ hS hv (by omega) i he) hz B
   obtain ⟨c,hf,hc⟩:= hp.buy P rfl s m i hv hZ he; let M:=stamping Q! s; have hp:mortgage M P m c:=⟨⟨hf.1.pos,hf.1.high,hf.1.low⟩,hf.2⟩
   let f(x):= purse Dean (hatW x) p; have hz:Run atTop id f 0:= Run.Ypow tendsto_id (Run.stanza tendsto_id) _
   let g(x:ℝ):=Cane.value (αm x) M.C M.A M.E M.s M.sway/P.L.val; have hh:Tendsto g atTop (𝓝 (Cane.value 0 M.C M.A M.E M.s M.sway/P.L.val)):=by
         have hx: Continuous (fun x:ℝ=>Cane.value x M.C M.A M.E M.s M.sway) :=by unfold Cane.value Cane.candle Measuring.factor; fun_prop
         exact (hx.continuousAt.tendsto.comp (Geneva.ray (X:=id) tendsto_id)).div_const _
   have hY:=Geneva.receipt O W H H' P X h hk hU hχ M u hr rfl hm hp.1 le_rfl hS hc f hz -- adjust
   exact ((ht.and hY).and (hh.eventually (ge_mem_nhds hp.2))).mono (fun x ⟨⟨h,hq⟩,hr⟩=>⟨h,hq hr⟩)
end YM.MSbar.Ballet
