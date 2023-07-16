// To configure the CS we will need some tools that are global for the CS (not tied to specific gates),
// so we do the same thing as with gates and do the inlining trick to have access to those tools

use std::any::TypeId;

pub trait StaticToolboxHolder: 'static + Send + Sync {
    // we can walk over and get the next one
    type DescendantHolder<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync>: StaticToolboxHolder;

    fn tool_exists<M: 'static + Send + Sync>(&self) -> bool;
    fn get_tool<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync>(&self) -> Option<&T>;
    fn get_tool_mut<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync>(
        &mut self,
    ) -> Option<&mut T>;

    fn add_tool<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync>(
        self,
        tool: T,
    ) -> Self::DescendantHolder<M, T>;
}

#[derive(Clone)]
pub struct EmptyToolbox;

impl StaticToolboxHolder for EmptyToolbox {
    type DescendantHolder<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync> =
        ToolsTuple<M, T, Self>;
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
    ) -> Self::DescendantHolder<M, T> {
        ToolsTuple {
            marker: std::marker::PhantomData,
            tool,
            other: self,
        }
    }
}

// We assume that any type ID can have only one parameter
pub struct ToolsTuple<
    M: 'static + Send + Sync + Clone,
    T: 'static + Send + Sync,
    U: StaticToolboxHolder,
> {
    marker: std::marker::PhantomData<M>,
    tool: T,
    other: U,
}

impl<MM: 'static + Send + Sync + Clone, TT: 'static + Send + Sync, U: StaticToolboxHolder>
    StaticToolboxHolder for ToolsTuple<MM, TT, U>
{
    type DescendantHolder<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync> =
        ToolsTuple<M, T, Self>;

    #[inline(always)]
    fn tool_exists<M: 'static + Send + Sync>(&self) -> bool {
        if std::any::TypeId::of::<M>() == std::any::TypeId::of::<MM>() {
            true
        } else {
            self.other.tool_exists::<M>()
        }
    }
    #[inline(always)]
    fn get_tool<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync>(&self) -> Option<&T> {
        if std::any::TypeId::of::<M>() == std::any::TypeId::of::<MM>() {
            unsafe {
                let casted: &T = &*(&self.tool as *const TT).cast() as &T;

                Some(casted)
            }
        } else {
            self.other.get_tool::<M, T>()
        }
    }
    #[inline(always)]
    fn get_tool_mut<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync>(
        &mut self,
    ) -> Option<&mut T> {
        if std::any::TypeId::of::<M>() == std::any::TypeId::of::<MM>() {
            unsafe {
                let casted: &mut T = &mut *(&mut self.tool as *mut TT).cast() as &mut T;

                Some(casted)
            }
        } else {
            self.other.get_tool_mut::<M, T>()
        }
    }
    #[inline(always)]
    fn add_tool<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync>(
        self,
        tool: T,
    ) -> Self::DescendantHolder<M, T> {
        if self.tool_exists::<M>() {
            panic!(
                "Tool type {} is already in the system",
                std::any::type_name::<M>()
            );
        }

        ToolsTuple {
            marker: std::marker::PhantomData,
            tool,
            other: self,
        }
    }
}

// We assume that any type ID can have only one parameter
pub struct DynTools {
    is_placeholder: bool,
    marker_type_id: TypeId,
    tool_type_id: TypeId,
    tool: Box<dyn std::any::Any + 'static + Send + Sync>,
    other: Box<Self>,
}

impl StaticToolboxHolder for DynTools {
    type DescendantHolder<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync> = Self;

    #[inline(always)]
    fn tool_exists<M: 'static + Send + Sync>(&self) -> bool {
        if self.is_placeholder {
            return false;
        }
        if std::any::TypeId::of::<M>() == self.marker_type_id {
            true
        } else {
            self.other.tool_exists::<M>()
        }
    }
    #[inline(always)]
    fn get_tool<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync>(&self) -> Option<&T> {
        if self.is_placeholder {
            return None;
        }
        if std::any::TypeId::of::<M>() == self.marker_type_id
            && std::any::TypeId::of::<T>() == self.tool_type_id
        {
            let casted: &T = self.tool.downcast_ref::<T>().expect("types must match");

            Some(casted)
        } else {
            self.other.get_tool::<M, T>()
        }
    }
    #[inline(always)]
    fn get_tool_mut<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync>(
        &mut self,
    ) -> Option<&mut T> {
        if self.is_placeholder {
            return None;
        }
        if std::any::TypeId::of::<M>() == self.marker_type_id
            && std::any::TypeId::of::<T>() == self.tool_type_id
        {
            let casted: &mut T = self.tool.downcast_mut::<T>().expect("types must match");

            Some(casted)
        } else {
            self.other.get_tool_mut::<M, T>()
        }
    }
    #[inline(always)]
    fn add_tool<M: 'static + Send + Sync + Clone, T: 'static + Send + Sync>(
        self,
        tool: T,
    ) -> Self::DescendantHolder<M, T> {
        if self.tool_exists::<M>() {
            panic!(
                "Tool type {} is already in the system",
                std::any::type_name::<M>()
            );
        }

        DynTools {
            is_placeholder: false,
            marker_type_id: TypeId::of::<M>(),
            tool_type_id: TypeId::of::<T>(),
            tool: Box::new(tool),
            other: Box::new(self),
        }
    }
}
