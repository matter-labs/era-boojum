pub trait BigArraySerde<'de>: Sized {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer;
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>;
}

impl<'de, T, const N: usize> BigArraySerde<'de> for [T; N]
where
    T: serde::Serialize + serde::Deserialize<'de>,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use serde::ser::SerializeTuple;
        let mut seq = serializer.serialize_tuple(N)?;
        for elem in &self[..] {
            seq.serialize_element(elem)?;
        }
        seq.end()
    }

    fn deserialize<D>(deserializer: D) -> Result<[T; N], D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct ArrayVisitor<T, const M: usize> {
            element: std::marker::PhantomData<T>,
        }

        impl<'de, T, const M: usize> serde::de::Visitor<'de> for ArrayVisitor<T, M>
        where
            T: serde::Deserialize<'de>,
        {
            type Value = [T; M];

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str(&format!("an array of length {}", M))
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<[T; M], A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let mut arr = Vec::with_capacity(M);
                for i in 0..M {
                    let el = seq
                        .next_element()?
                        .ok_or_else(|| serde::de::Error::invalid_length(i, &self))?;
                    arr.push(el);
                }
                let arr: [T; M] = arr
                    .try_into()
                    .map_err(|_| serde::de::Error::invalid_length(M, &self))?;

                Ok(arr)
            }
        }

        let visitor = ArrayVisitor::<_, N> {
            element: std::marker::PhantomData,
        };
        deserializer.deserialize_tuple(N, visitor)
    }
}

pub struct BigArrayRefWrapper<'de, B: BigArraySerde<'de>>(&'de B);

impl<'de, B: BigArraySerde<'de>> serde::Serialize for BigArrayRefWrapper<'de, B> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.0.serialize(serializer)
    }
}

pub struct BigArrayWrapper<'de, B: BigArraySerde<'de>>(B, std::marker::PhantomData<&'de ()>);

impl<'de, B: BigArraySerde<'de>> serde::Serialize for BigArrayWrapper<'de, B> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.0.serialize(serializer)
    }
}

impl<'de, B: BigArraySerde<'de>> serde::Deserialize<'de> for BigArrayWrapper<'de, B> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let new = B::deserialize(deserializer)?;

        Ok(Self(new, std::marker::PhantomData))
    }
}
