import YM.MS.Motif.Shift

set_option autoImplicit false
noncomputable section
namespace YM.MS.Mach
open Set Filter Function Finset Metric Real
open Book Convolve
open Motif Literal
open scoped Topology
variable {E J M:Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup J] [Module ℂ J] [ AddCommGroup M] [Module ℂ M]
def Present (f:ℂ→E): Prop:= ∃ V:Box E, (fun z=> value E z V)=f
variable {f g:ℂ→E} {a:ℂ→J}
namespace Present
lemma here (x:E): Present (fun _:ℂ=>x):= ⟨Finsupp.single 0 x,funext fun z=>by rw [value_sl,pow_zero,one_smul]⟩
lemma uline (p:ℕ): Present (fun z:ℂ=>z^p):= ⟨ Finsupp.single p (1:ℂ),funext fun z=> by rw [ value_sl, smul_eq_mul,mul_one]⟩
lemma add (h:Present f)(he: Present g): Present (fun z=> f z+g z):= by obtain ⟨V,rfl⟩:=h; obtain ⟨W,rfl⟩:=he; exact ⟨V+W, funext fun z=> map_add _ _ _ ⟩
lemma grows (h:Present f)(K:E→ₗ[ℂ] M) : Present (fun z=> K (f z)):= by obtain ⟨V,rfl⟩:=h; exact ⟨_,funext fun z=> linear_v V K z⟩
lemma pair (h:Present f)(hv:Present a)(K:E→ₗ[ℂ] J→ₗ[ℂ] M) : Present (fun z=> K (f z) (a z)):= by obtain ⟨V,rfl⟩:=h; obtain ⟨W,rfl⟩:=hv; exact ⟨_,funext fun z=>(pair_v V W K z).symm⟩
lemma smul (h:Present f)(z:ℂ): Present ( z • f ):= by obtain ⟨V,rfl⟩:=h; exact ⟨_,funext fun s=> map_smul _ z V⟩
lemma step (h: Present f): Present (fun z=> z • f z):= by
   have he: Present fun z:ℂ=>z:= by simpa using uline 1
   exact he.pair h ( LinearMap.lsmul ℂ E )
end Present
end YM.MS.Mach
