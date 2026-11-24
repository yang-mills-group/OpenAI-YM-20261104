import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphAnchor
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphRevenue
open YM YM.FVA2 YM.FVA2.O YM.FVA2.O.Score YM.FVA2.O.Enh YM.FVA2.O.Project
open Set Filter YangMills.MSbar IssuedMaxwell.Reports IssuedMaxwell.GraphCorrelation
open scoped BigOperators Classical Topology
variable (g:YangMills.GaugeGroup){n m:ℕ}

def due (a:Fin n→Ordinary.Label (B g))(p:Ordinary.Price (B g) n)(b:Fin m→Ordinary.Label (B g))
    (h k:ℕ)(t:ℝ)(x:Points n)(y:Points m):ℂ:=
  read g (n+m) k (Fin.append a b) (forest (squeeze t x) y)-
    Ordinary.truncation (B g) (read g) p (sky g a) h k b t x y
def rate (a:Fin n→Ordinary.Label (B g))(h:ℕ):ℝ:=(h:ℝ)+1-(sky g a:ℝ)
theorem paid (a:Fin n→Ordinary.Label (B g))(p:Ordinary.Price (B g) n)
    (sale:Ordinary.ExteriorExpansion (B g) (read g) a p)(K:Set (Points n))(ck:IsCompact K)(sep:K⊆conf n)
    (b:Fin m→Ordinary.Label (B g))(E:Set (Points m))(ce:IsCompact E)(ext:E⊆Outside m)(h k:ℕ):
    Rain (rate g a h) (fun (i:K×E)(t:ℝ)=>due g a p b h k t i.1.val i.2.val):=by
  obtain ⟨C,pos,L,cash⟩:=sale.exterior K ck sep m b E ce (fun y hy=>(GraphOutside.original y).mp (ext hy)) h k
  refine ⟨C,pos,L,?_⟩
  filter_upwards [cash] with t bound
  intro i
  have wage:=bound i.1.val i.1.property i.2.val i.2.property
  change ‖due g a p b h k t i.1.val i.2.val‖≤C*(1+t)^L*Real.exp (((sky g a:ℝ)-(h:ℝ)-1)*t) at wage
  simpa only [rate,post,neg_sub,sub_sub,neg_add_rev,neg_neg,mul_assoc] using wage

theorem change (a a₀:Fin n→Ordinary.Label (B g))(h:ℕ){I:Type}{f:I→ℝ→ℂ}
    (purchase:Rain (rate g a h) f):Rain (rate g a₀ h) (fun i t=>
      (Real.exp (((sky g a₀:ℝ)-(sky g a:ℝ))*t):ℂ)*f i t):=by
  let delta:ℝ:=(sky g a:ℝ)-(sky g a₀:ℝ)
  have fared:Rain delta (fun (_:I)(t:ℝ)=>fee t delta):=Rain.all_fee
  have shift:delta+rate g a h=rate g a₀ h:=by unfold delta rate;ring
  have same (t:ℝ):fee t delta=(Real.exp (((sky g a₀:ℝ)-(sky g a:ℝ))*t):ℂ):=by
    unfold fee delta
    congr 2
    ring
  have cash:=fared.mul purchase
  simpa only [shift,same] using cash
end IssuedMaxwell.GraphRevenue
end
