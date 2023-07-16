// To configure the CS we will need some tools that are global for the CS (not tied to specific gates),
// so we do the same thing as with gates and do the inlining trick to have access to those tools

pub trait StaticToolboxHolder: 'static + Send + Sync {
    fn tool_exists<M: 'static + Send + Sync>(&self) -> bool;
    fn get_tool<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync>(&self) -> Option<&T>;
    fn get_tool_mut<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync>(
        &mut self,
    ) -> Option<&mut T>;
    fn add_tool<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync>(
        self,
        tool: T,
    ) -> (Tool<M, T>, Self);
}

impl StaticToolboxHolder for () {
    #[inline(always)]
    fn tool_exists<M: 'static + Send + Sync>(&self) -> bool {
        false
    }
    #[inline(always)]
    fn get_tool<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync>(&self) -> Option<&T> {
        None
    }
    #[inline(always)]
    fn get_tool_mut<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync>(
        &mut self,
    ) -> Option<&mut T> {
        None
    }
    #[inline(always)]
    fn add_tool<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync>(
        self,
        tool: T,
    ) -> (Tool<M, T>, Self) {
        (
            Tool {
                marker: std::marker::PhantomData,
                tool,
            },
            (),
        )
    }
}

// We assume that any type ID can have only one parameter
pub struct Tool<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync> {
    marker: std::marker::PhantomData<&'static M>,
    tool: T,
}

impl<MM: 'static + Send + Sync + Clone, TT: 'static + Send + Sync, U: StaticToolboxHolder>
    StaticToolboxHolder for (Tool<MM, TT>, U)
{
    #[inline(always)]
    fn tool_exists<M: 'static + Send + Sync>(&self) -> bool {
        if std::any::TypeId::of::<M>() == std::any::TypeId::of::<MM>() {
            true
        } else {
            self.1.tool_exists::<M>()
        }
    }
    #[inline(always)]
    fn get_tool<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync>(&self) -> Option<&T> {
        if std::any::TypeId::of::<M>() == std::any::TypeId::of::<MM>() {
            unsafe {
                let casted: &T = &*(&self.0.tool as *const TT).cast() as &T;

                Some(casted)
            }
        } else {
            self.1.get_tool::<M, T>()
        }
    }
    #[inline(always)]
    fn get_tool_mut<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync>(
        &mut self,
    ) -> Option<&mut T> {
        if std::any::TypeId::of::<M>() == std::any::TypeId::of::<MM>() {
            unsafe {
                let casted: &mut T = &mut *(&mut self.0.tool as *mut TT).cast() as &mut T;

                Some(casted)
            }
        } else {
            self.1.get_tool_mut::<M, T>()
        }
    }
    #[inline(always)]
    fn add_tool<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync>(
        self,
        tool: T,
    ) -> (Tool<M, T>, Self) {
        if self.tool_exists::<M>() {
            panic!(
                "Tool type {} is already in the system",
                std::any::type_name::<M>()
            );
        }

        (
            Tool {
                marker: std::marker::PhantomData,
                tool,
            },
            self,
        )
    }
}
