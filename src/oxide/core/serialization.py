import pickle

from oxide.core import config

from typing import Any

VALID_SERIAL = ['pickle']
try:
    import msgpack
    VALID_SERIAL.append('msgpack')
except ImportError:
    pass

SERIAL_METHOD = config.datastore_serialization
if SERIAL_METHOD not in VALID_SERIAL:
    SERIAL_METHOD = 'pickle'

def serialize(data: Any) -> bytes:
    global SERIAL_METHOD
    res = None
    # data_converted = {k: list(v) if isinstance(v, set) else v for k, v in data.items()}
    data_converted = data

    if SERIAL_METHOD == 'pickle':
        res = pickle.dumps(data_converted)
    elif SERIAL_METHOD == 'msgpack':
        res = msgpack.dumps(data_converted)
    return res

def deserialize(data: bytes) -> Any:
    global SERIAL_METHOD
    res = None
    
    if SERIAL_METHOD == 'pickle':
        res = pickle.loads(data)
    elif SERIAL_METHOD == 'msgpack':
        res = msgpack.loads(data, strict_map_key=False)
    return res